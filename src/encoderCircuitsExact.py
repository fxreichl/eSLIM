from encoderCircuits import EncoderCircuits

class EncoderExactSynthesis(EncoderCircuits) :

  # gates a list of the shape (var, lines), where var is the alias and lines define the gate
  def __init__(self, inputs, outputs, gates, cycle_candidates, config) :
    self.inputs = inputs
    self.subcircuit_outputs = outputs
    self.gates = gates
    self.forbidden = cycle_candidates
    self.potential_cycle_found = len(self.forbidden) > 0
    self.config = config
    assert len(inputs) > 0 and len(outputs) > 0
    self.last_used_variable = max(self.inputs)
    self.last_used_variable = max(max(self.subcircuit_outputs),self.last_used_variable)
    self.last_used_variable = max(max([x for x,_,_ in gates]), self.last_used_variable)
    self.descendants_renaming = {}
    for alias in self.subcircuit_outputs :
      self.descendants_renaming[alias] = self._getNewVariable()
    self.max_var_specification_representation = self.last_used_variable
    self.allow_xors = False
    self.writeComments = True
    self.debug = False
    self.internal_gates = []
    self.selection_variables = []
    self.gate_definition_variables = []
    self.gate_output_variables = []
    self.useTrivialRuleConstraint = config.useTrivialRuleConstraint
    self.useNoReapplicationConstraint = config.useNoReapplicationConstraint
    self.useAllStepsConstraint = config.useAllStepsConstraint
    self.useOrderedStepsConstraint = config.useOrderedStepsConstraint
    # If true, we introduce for each gate and for each of its inputs a variable that represents the input.
    # The aim of this approach is to reduce the number of gates that need to be introduced for k-LUTs with larger k.
    self.use_gate_input_variables = False

  def _writeSpecification(self) :
    for gate in self.gates :
      alias, anded, lines = gate
      self._writeGate(alias, anded, lines)

  def _writeEquivalenceConstraints(self) :
    self._setupSubcircuitOutputVariables()
    self._writeComment("Establish equivalence between specification and encoding")
    for spec_out in self.subcircuit_outputs :
      out_name = self.descendants_renaming[spec_out]
      c = self._getNewVariable()
      self._writeEquivalence(c, spec_out, out_name)
      self.constraintGates += [c]

  def _getUniversallyQuantifiedVariables(self) :
    return ", ".join(str(x) for x in self.inputs)

  def getSubcircuitInputs(self) :
    return self.inputs

  def _writeSpecificationCopy(self) :
    pass