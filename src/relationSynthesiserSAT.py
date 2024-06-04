import bitarray
import bitarray.util
import time
import logging

from bindings.build.relationSynthesiser import RelationSynthesiser as RSynth
from bindings.build.relationSynthesiser import Configuration as ConfigC


from utils import Configuration
from utils import ViolatedInvariantException

class RelationSynthesiser :
    
  # Input Condition: All assignments of the inputs in the relation need to be sorted equally.
  def __init__(self, inputs, outputs, potential_cycles, relation, config : Configuration) :
    self.inputs = inputs
    self.outputs = outputs
    self.nof_gate_inputs = config.gate_size
    self.potential_cycles = potential_cycles
    self.relation = relation
    self.config = config

  def setTimeingManager(self, timer) :
    self.timer = timer

  def setLogger(self, logger) :
    self.logger = logger

  # return status, synthesised circuit
  # status 0: new circuit computed
  # status 1: no circuit could be computed because of a timeout
  # status 2: no circuit could be computed unspecified reason
  # status -1: Given relation could not be realised
  # deprecated status 2: no circuit could be computed because of a memory-out
  def synthesise(self, nof_gates, nof_gate_inputs, gate_names, check_initial) :
    self.nof_gates = nof_gates
    cfg = ConfigC(nof_gate_inputs, self.config.synthesiseAig, self.config.allowConstantsAsOutputs, 
                  self.config.allowInputsAsOutputs, self.config.useTrivialRuleConstraint, self.config.useAllStepsConstraint, 
                  self.config.useNoReapplicationConstraint, self.config.useOrderedStepsConstraint)
    encoding_start = time.time()
    # try :
    synthesiser = RSynth(self.relation, self.potential_cycles, self.inputs, self.outputs, nof_gates, cfg)
    # except MemoryError:
    #    # the encoding may get too large.
    #   return 2, None
  
    self.timer.logEncodingTime(time.time() - encoding_start)
    model = None
    if self.timer.useTimeout() and not self.timer.isTimeoutSet(nof_gates) :
      self.timer.initTimeout(nof_gates)
    if check_initial :
      status = self._checkSize(synthesiser, nof_gates)
      if status == 20 and self.config.useNoReapplicationConstraint:
        synthesiser.toggleNoReapplicationRule()
        status = self._checkSize(synthesiser, nof_gates)
        synthesiser.toggleNoReapplicationRule()
      if status == 20 :
        logging.warning("Warning: Relation could not be represented")
        return -1, None
      elif status == 10 :
        model = synthesiser.getModel()
      # elif status == 30 :
      #   return 2, None
      else :
        return 1, None
    
    next_size_to_check = nof_gates - 1
    while next_size_to_check >= 0 and self._checkSize(synthesiser, next_size_to_check) == 10 :
      model = synthesiser.getModel()
      next_size_to_check -= 1
    circuit_size = next_size_to_check + 1
    if self.config.allowConstantsAsOutputs or self.config.allowInputsAsOutputs and  circuit_size > 0 :
      if self._checkSize(synthesiser, 0) == 10 :
        model = synthesiser.getModel()
        circuit_size = 0
    if model is None :
      assert not check_initial
      return 3, None
    return 0, self._extractCircuitFromAssignment(model, circuit_size, gate_names, synthesiser)
    
      
      
  def _checkSize(self, synth, size) :
    assert size >= 0, f"Invalid size given: {size}"
    self.logger.logCheckedSize(size)
    start_time = time.time()
    # try :
    if self.timer.useTimeout() :
      timeout = self.timer.getTimeout(size)
      result = synth.checkSizeTO(size, timeout)
    else :
      result = synth.checkSize(size)
      assert result == 10 or result == 20, f"Invalid status: {result}"
    # except MemoryError:
    #   return 30
    used_time = time.time() - start_time
    if result == 10 :
      self.timer.logSatTiming(size, used_time, len(self.inputs), len(self.outputs))
      if self.timer.useTimeout() :
        self.timer._updateTimeouts(size)
    elif result == 20 :
      self.timer.logUnsatTiming(size, used_time, len(self.inputs), len(self.outputs))
    else :
      self.timer.logTimeout(size, len(self.inputs), len(self.outputs))
    return result
  
  # self.solver must not be None and it must be in the SAT state
  def _extractCircuitFromAssignment(self, model, size, gate_names, synthesiser) :
    assert size <= len(gate_names)
    model_set = set(model)
    gates = []
    output_association = {} # associates the new outputs of the subcircuit to the old outputs
    selection_variables = synthesiser.getSelectionVariables()
    gate_definition_variables = synthesiser.getDefinitionVariables()
    gate_output_variables = synthesiser.getOutputVariables()
    for i in range(size) :
      inputs = []
      for j, s in enumerate(selection_variables[i]) :
        if s in model_set :
          if j < len(self.inputs) :
            inputs.append(self.inputs[j])
          else :
            inputs.append(gate_names[j - len(self.inputs)])
      if len(inputs) != self.nof_gate_inputs :
        raise ViolatedInvariantException(f"Gate with {len(inputs)} activate selection variables found -- {self.config.gate_size} variables need to be active.")
      # assert len(inputs) == self.nof_gate_inputs, f"#active selection variables: {len(inputs)}; gate size: {self.nof_gate_inputs}"
      gate_definitions = bitarray.util.zeros(2 ** self.nof_gate_inputs)
      for j, gv in enumerate(gate_definition_variables[i], start=1) :
        if gv in model_set :
          gate_definitions[j] = 1
      gates += [(gate_names[i], inputs, gate_definitions)]

      for j, o in enumerate(gate_output_variables[i]) :
        if o in model_set :
          output_association[self.outputs[j]] = gate_names[i]

    if self.config.allowInputsAsOutputs :
      for i in range(self.nof_gates, self.nof_gates + len(self.inputs)) :
        for j, o in enumerate(gate_output_variables[i]) :
          if o in model_set :
            output_association[self.outputs[j]] = self.inputs[i-self.nof_gates]
    if self.config.allowConstantsAsOutputs :
      for j, o in enumerate(gate_output_variables[-1]) : 
        if o in model_set :
          output_association[self.outputs[j]] = None
    
    assert len(output_association) == len(self.outputs), "Unset output detected"
    return (gates, output_association)

