from sys import stdout
import time

import blifIO
from utils import NoOutputException
from utils import Configuration
from utils import ViolatedInvariantException

class EncoderCircuits :


  def __init__(self, specification, gates_to_replace, dependency_constraints, config : Configuration, timer) :
    start = time.time()
    self.specification = specification
    self.to_replace = gates_to_replace
    self.config = config
    self.timer = timer
    self.last_used_variable = specification.max_var
    self.allow_xors = False
    # self.writeComments = False
    self.writeComments = True
    self.debug = False
    self._getSubcircuitIO()
    self._analyse_subcircuit()
    self.potential_cycle_found = len(self.forbidden) > 0
    self._processDependencyConstraints(dependency_constraints)
    self.forbidden = [(x,self.descendants_renaming[y]) for x,y in self.forbidden]
    self.max_var_specification_representation = self.last_used_variable
    self.internal_gates = []
    self.selection_variables = []
    self.gate_definition_variables = []
    self.gate_output_variables = []

    self.useTrivialRuleConstraint = config.useTrivialRuleConstraint
    self.useNoReapplicationConstraint = config.useNoReapplicationConstraint
    self.useAllStepsConstraint = config.useAllStepsConstraint
    self.useOrderedStepsConstraint = config.useOrderedStepsConstraint

    timer.encoder_setup += (time.time() - start)

  def hasPotentialCycles(self) :
    return len(self.forbidden) > 0

  def getEncoding(self, nof_gates, nof_gate_inputs, out, ) :
    # We only allow gates with exactly nof_gate_inputs inputs.
    # Thus, if the subcircuit has fewer inputs we cannot construct gates 
    assert len(self.inputs) >= nof_gate_inputs, "The specification must have more inputs than the gates"
    self.nof_gates = nof_gates
    self.nof_gate_inputs = nof_gate_inputs
    self.out = out
    self._resetEncoder()
    self._writePrefix()
    self._writeComment("Specification")
    self._writeSpecification()
    if self.potential_cycle_found :
      self._writeSpecificationCopy()
    for i in range(self.nof_gates) :
      self._writeGateConstraints(i)
    if len(self.forbidden) > 0 :
      self._writeComment("Cycle Constraint")
      self._writeCycleConstraint()
      self._setupSubcircuitOutputVariables()
    else :
      self._setupSubcircuitOutputs()
    self._addSymmetryBreakingConstraints()
    if self.config.synthesiseAig :
      self._writeAigerConstraints()
    self._writeComment("Specification Copy")
    if not self.potential_cycle_found :
      self._writeSpecificationCopy()
    self._writeEquivalenceConstraints()
    self.setupOutput()

  def setupOutput(self) :
    self._writeAnd(self.output_var, self.constraintGates)

  # Symmetry breaking constraints may prevent the realisation of a circuit.
  # The method disables the problematic constraints
  def disableSymmetryBreaking(self) :
    self.useNoReapplicationConstraint = False
    # We do not disable the ordered steps rule as it cannot prevent a realisation
    # We do not disable the all steps rule as we do not want gates that are unused

  def getSelectionVariables(self) :
    return self.selection_variables

  def getGateDefinitionVariables(self) :
    return self.gate_definition_variables

  def getGateOutputVariables(self) :
    return self.gate_output_variables

  def getSubcircuitInputs(self) :
    return self.subcircuit_inputs

  def getSubcircuitOutputs(self) :
    return self.subcircuit_outputs


  def _writePrefix(self) :
    self.out.write("#QCIR-G14\n")
    outermost_existentials = self._setupCircuitVariables()
    outermost_existentials += [x for y in self.connection_variables.values() for x in y]
    outermost_existentials_str = ", ".join([str(x) for x in outermost_existentials])
    self.out.write("exists(" + outermost_existentials_str + ")\n")
    input_str = self._getUniversallyQuantifiedVariables()
    self.out.write("forall(" + input_str + ")\n")
    self.internal_gates = tuple(self._getNewVariable() for x in range(self.nof_gates))    
    # If forbidden is not empty the subcircuit depends on the copy of the specification.
    # As the copy of the specification also depends on the subcircuit and the topology of the subcircuit is not fixed.
    # we do not know the appropriate ordering for the gates (QCIR gates must be sorted topologically).
    # If forbidden is empty then the subcircuit does not depend on the copy of the specification.
    # Thus we can define the outputs by gates (without quantified variables)
    if self.potential_cycle_found :
      # All successors of the subcircuit must occur after the gates of the subcircuit in the encoding.
      # This is necessary as each gate could depend on each gate in subcircuit and as a qcir encoding must be sorted topologically.
      # If there is a potential cycle there are also successor gates which are used as inputs.
      # The gates must defined before the subcircuit in the encoding. 
      # As these successors cannot be defined before and afterwards we cannot use a gate for the representation of the output.
      # Instead we use an existentially quantified variable.
      # Variables that represent the value of each output of the subcircuit
      subcircuit_output_variables_str = ", ".join(str(self.descendants_renaming[x]) for x in self.subcircuit_outputs)
      self.out.write("exists(" + subcircuit_output_variables_str + ")\n")
    self.output_var = self._getNewVariable()
    self.out.write("output({})\n".format(self.output_var))


  def _writeSpecification(self) :
    x = time.time()
    for gate in self.specification.orderedGateTraversal() :
      alias = gate.getAlias()
      anded, lines = gate.getQCIRGates()
      self._writeGate(alias, anded, lines)
    self.timer.encode_specification += (time.time() - x)

  def _writeGateConstraints(self, gate_id) :
    x = time.time()
    self._writeComment(f"Constraints for selection variables at gate {gate_id}")
    self._constrainSelectionVariables(gate_id)
    self._writeComment(f"Semantic Constraints gate {gate_id}")
    self._restrictGateSemantic(gate_id)
    self.timer.encode_gate_constraints += (time.time() - x)
    

  # If there are no potential cycles we can directly define the outputs of the circuits by gates
  def _setupSubcircuitOutputs(self) :
    for idx, out in enumerate(self.subcircuit_outputs) :
      self._writeComment(f"Subcircuit output cardinality constraints for output {idx}")
      vars = [x[idx] for x in self.gate_output_variables]
      self._addCardinalityConstraint(vars, 1)
      self._writeComment(f"Subcircuit output var definition for output {idx}")
      defining_and_gates = []
      sub_circ_out = self.descendants_renaming[out]
      for i in range(self.nof_gates) :
        in_node1 = self._getGate(i)
        and_gate = self._getNewVariable()
        defining_and_gates.append(and_gate)
        self._writeAnd(and_gate, [self.gate_output_variables[i][idx], in_node1])
      if self.config.allowInputsAsOutputs :
        for i in range(self.nof_gates, self.nof_gates + len(self.inputs)) :
          input_var = self.inputs[i - self.nof_gates]
          and_gate = self._getNewVariable()
          defining_and_gates.append(and_gate)
          self._writeAnd(and_gate, [self.gate_output_variables[i][idx], input_var])
      # We only ask when is the output true. As a constant output must be false (normality) we do not need to consider it here.
      # self._writeAnd(sub_circ_out, defining_and_gates)
      self._writeOr(sub_circ_out, defining_and_gates)

  def _writeConditionalEquivalence(self, out_var, cond_var, in1, in2) :
    or1 = self._getNewVariable()
    self._writeOr(or1, [-cond_var, -in1, in2])
    or2 = self._getNewVariable()
    self._writeOr(or2, [-cond_var, in1, -in2])
    self._writeAnd(out_var, [or1, or2])

  # If there are potential cycles then the direct encoding does not fulfil the 
  # QCIR ordering constraints (a gate must be introduced when it is used) 
  def _setupSubcircuitOutputVariables(self):
    for idx, out in enumerate(self.subcircuit_outputs) :
      self._writeComment(f"Subcircuit output cardinality constraints for output {idx}")
      vars = [x[idx] for x in self.gate_output_variables]
      self._addCardinalityConstraint(vars, 1)
      self._writeComment(f"Subcircuit output var definition for output {idx}")
      sub_circ_out = self.descendants_renaming[out]
      for i in range(self.nof_gates) :
        in_node1 = self._getGate(i)
        c = self._getNewVariable()
        self._writeConditionalEquivalence(c, self.gate_output_variables[i][idx], in_node1, sub_circ_out)
        self.constraintGates += [c]
      if self.config.allowInputsAsOutputs :
        for i in range(self.nof_gates, self.nof_gates + len(self.inputs)) :
          input_var = self.inputs[i - self.nof_gates]
          c = self._getNewVariable()
          self._writeConditionalEquivalence(c, self.gate_output_variables[i][idx], input_var, sub_circ_out)
          self.constraintGates += [c]
      if self.config.allowConstantsAsOutputs :
        c = self._getNewVariable()
        # As we have normal gates a constant output can only be false.
        # Thus, if the corresponding gate_output_variable is true, then the subcircuit variable needs to be false.
        self._writeOr(c, [-self.gate_output_variables[-1][idx], -sub_circ_out])
        self.constraintGates += [c]
      

  def _addSymmetryBreakingConstraints(self) :
    x = time.time()
    if self.useTrivialRuleConstraint :
      self._writeComment("Non-trivial constraints")
      self._addNonTrivialConstraint()
    if self.useAllStepsConstraint :
      self._writeComment("Use all steps constraints")
      self._addUseAllStepsConstraint()
    if self.useNoReapplicationConstraint :
      self._writeComment("No reapplication constraints")
      self._addNoReapplicationConstraint()
    if self.useOrderedStepsConstraint :
      self._writeComment("Ordered steps constraints")
      self._addOrderedStepsConstraint()
    self.timer.encode_symmetry_breaking_constraints += (time.time() - x)

  # The non trivial rule, restricts projections to inputs and constants
  # The only normal non-AIG gate that remains is the XOR.
  def _writeAigerConstraints(self) :
    assert self.nof_gate_inputs == 2, "An AIG gates must have two inputs"
    assert self.useTrivialRuleConstraint
    self._writeComment("AIGER Constraints")
    for i in range(self.nof_gates) :
      constraint_var = self._getNewVariable()
      # Forbid XOR-gates
      self._writeOr(constraint_var, [-self.gate_definition_variables[i][0], -self.gate_definition_variables[i][1], self.gate_definition_variables[i][2]])
      # Forbid OR-gates -- Optional constraints we can remove OR-Gates without increasing the number of gates
      # self._writeOr(constraint_var, [-self.gate_definition_variables[i][0], -self.gate_definition_variables[i][1], -self.gate_definition_variables[i][2]])
      self.constraintGates += [constraint_var]

  # if self.forbidden is not empty we know that there is at least one gate in the specification that is both a descendant and an ancestor of the gates that shall be removed.
  # We have to ensure that that the encoding does not allow cyclic circuits.
  def _writeCycleConstraint(self) :
    assert len(self.forbidden) > 0, "Cycle rules shall only be written if there are forbidden pairs"
    self._writeComment("Connection Variables Base")
    self._setupConnectionvariables()

    if len(self.forbidden) > 1 :
      self._writeComment("Multiple Forbidden")
      self._writeCombinedCycleRule()

    self._writeComment("Cycle Restrictions")
    self._writeGateOutputCycleConstraints()

  def _writeSpecificationCopy(self) :
    x = time.time()
    for gate in self.specification.orderedGateTraversal() :
      if gate.getAlias() in self.gates_to_copy :
        assert not gate.isConstant(), "A constant gate cannot be the successor of a replaced gate"
        renamed_alias = self.descendants_renaming[gate.getAlias()]
        inputs = [self.descendants_renaming[x] if x in self.descendants_renaming else x for x in gate.inputs]
        # Gates that need to be copied have to be successors of removed gates. 
        # Every successor of a removed gate must have at least one renamed input.
        # assert inputs != gate.inputs
        if inputs == gate.inputs :
          raise ViolatedInvariantException(f"No input of a copied gate is a descendant - alias: {gate.getAlias()}")
        anded, lines = gate.getQCIRGates(inputs)
        self._writeGate(renamed_alias, anded, lines)
    self.timer.encode_specification_copy += (time.time() - x)

  def _writeEquivalenceConstraints(self) :
    self._writeComment("Establish equivalence between specification and copy")
    for spec_out in self.specification.getOutputs() :
      if spec_out in self.descendants_renaming:
        spec_out_copy = self.descendants_renaming[spec_out]
        c1 = self._getNewVariable()
        self._writeEquivalence(c1, spec_out, spec_out_copy)
        self.constraintGates += [c1]

  def _setupCircuitVariables(self) :
    variables = []
    self.selection_variables = tuple(tuple(self._getNewVariable() for _ in range(len(self.inputs) + y)) for y in range(self.nof_gates))
    variables += [sv for x in self.selection_variables for sv in x]

    # Suppose gates have n inputs i_1,...,i_n
    # The definition variables are ordered as follows
    #                   -i_1,...,-i_n not needed (normal gates)
    # def_var[0]        -i_1,...,-i_{n-1},i_n
    # def_var[1]        -i_1,...,-i_{n-2},i_{n-1},i_n
    # ...
    # def_var[2^n - 2]   i_1,...,i_n
    offset = 1 # We use normal gates
    self.gate_definition_variables = tuple(tuple(self._getNewVariable() for x in range(2 ** self.nof_gate_inputs - offset)) for _ in range(self.nof_gates))
    variables += [sv for x in self.gate_definition_variables for sv in x]

    self.gate_output_variables = list(tuple(self._getNewVariable() for _ in self.subcircuit_outputs) for _ in range(self.nof_gates))
    if self.config.allowInputsAsOutputs :
      self.gate_output_variables += [tuple(self._getNewVariable() for _ in self.subcircuit_outputs) for _ in self.inputs]
    if self.config.allowConstantsAsOutputs :
      self.gate_output_variables.append(tuple(self._getNewVariable() for _ in self.subcircuit_outputs))

    if len(self.inputs) == self.nof_gate_inputs :
      # Actually, we could also remove selection variables in this case.
      self.gate_input_variables = (tuple(self._getNode(idx) for idx in range(self.nof_gate_inputs)),) + tuple(tuple(self._getNewVariable() for _ in range(self.nof_gate_inputs)) for _ in range(self.nof_gates - 1))
    else :
      self.gate_input_variables = tuple(tuple(self._getNewVariable() for _ in range(self.nof_gate_inputs)) for _ in range(self.nof_gates))

    # TODO: inputs should always be allowed
    if self.config.allowInputsAsOutputs :
      self.connection_variables = {y : [self._getNewVariable() for _ in range(self.nof_gates + len(self.inputs))] for y in set(x for _, x in self.forbidden)}
    else :
      self.connection_variables = {y : [self._getNewVariable() for _ in range(self.nof_gates)] for y in set(x for _, x in self.forbidden)}

    variables += [sv for x in self.gate_output_variables for sv in x]
    return variables

  def _resetEncoder(self) :
    self.last_used_variable = self.max_var_specification_representation
    self.constraintGates = []

  
  def _getSubcircuitIO(self) :
    input_set = self.specification.getSubcircuitInputs(self.to_replace)
    output_set = self.specification.getSubcircuitOutputs(self.to_replace)
    if len(input_set) == 0 :
      print(f"to_replace: {self.to_replace}")
      print("Specification")
      blifIO.writeSpecification2Stream(stdout, self.specification, "error_model")
      assert False, "Subcircuit has no inputs" #TODO: should this really abort the program
    elif len(output_set) == 0 :
      raise NoOutputException
    self.subcircuit_inputs = list(input_set)
    self.subcircuit_outputs = list(output_set)
    x = time.time()
    self.forbidden = self.specification.getPotentialCycles(input_set, output_set, self.to_replace)
    self.timer.cyclic_pair_detection_time += time.time() - x


  def _analyse_subcircuit(self) :
    self.descendants_renaming = {}
    to_analyse = []
    # seen = set(self.subcircuit_outputs)
    seen = set(self.to_replace)
    for gate_var in self.subcircuit_outputs :
      self.descendants_renaming[gate_var] = self._getNewVariable()
      gate_outputs = self.specification.getGateOutputs(gate_var)
      to_analyse += [x for x in gate_outputs if not x in seen]
      seen.update(gate_outputs)

    self.gates_to_copy = set()

    while len(to_analyse) > 0 :
      gate_var = to_analyse.pop()
      if gate_var in self.to_replace :
        continue
      self.gates_to_copy.add(gate_var)
      self.descendants_renaming[gate_var] = self._getNewVariable()
      gate_outputs = self.specification.getGateOutputs(gate_var)
      to_analyse += [x for x in gate_outputs if not x in seen]
      seen.update(gate_outputs)
    
    if len(self.forbidden) > 0 : #CHECK:
      inputs_to_handle = set(x for _, x in self.forbidden)
      # If an input of the subcircuit is a successor of an output we have to use
      # the renaming of the gate. 
      self.inputs = [self.descendants_renaming[x] if x in inputs_to_handle else x for x in self.subcircuit_inputs]
    else :
      self.inputs = self.subcircuit_inputs
    
  def _processDependencyConstraints(self, dependency_constraints) :
    input_set = set(self.subcircuit_inputs)
    output_set = set(self.subcircuit_outputs)
    for _,_, tfi, tfo in dependency_constraints :
      x = input_set.intersection(tfo)
      y = output_set.intersection(tfi)
      if len(x) == 0 or len(y) == 0 :
        continue
      for i in x :
        for o in y :
          if (i,o) in self.forbidden :
            continue
          self.forbidden.append((i,o))

  def _constrainSelectionVariables(self, gate_index) :
    # cardinality = self.nof_gate_inputs
    selection_vars = self.selection_variables[gate_index]
    if len(selection_vars) == self.nof_gate_inputs :
      gate_var = self._getNewVariable()
      self._writeAnd(gate_var, selection_vars)
      self.constraintGates += [gate_var]
    else :
      self._setupSelectionVariableCounter(gate_index)

  def _setPolarity(self, variable, is_true) :
    if is_true == 1 : #true
      return variable
    else :
      return -variable 

  def _restrictGateSemantic(self, gate_index) :
    gate_input_vars = self.gate_input_variables[gate_index]
    defining_and_gates = []
    for i in range(1, 2 ** self.nof_gate_inputs) :
      polarities = self._getBits(i, self.nof_gate_inputs)
      conjuncts = [self._setPolarity(gi, polarities[j]) for j, gi in enumerate(gate_input_vars)]
      conjuncts.append(self._getGateDefinitionVariable(gate_index, i))
      and_gate = self._getNewVariable()
      defining_and_gates.append(and_gate)
      self._writeAnd(and_gate, conjuncts)
    out_node = self._getGate(gate_index)
    self._writeOr(out_node, defining_and_gates)


  # We introduce a sequential counter for the selection variables anyway in order to 
  # ensure that exactly self.nof_gate_inputs selection variables are true.
  # We want to use the sequential counter in order to restrict the gate inputs variables.
  # We apply the following idea:
  # If the kth input of the ith subcircuit of the counter is false buts its kth output is true,
  # then there are exactly k-1 enabled selection variables before the i+1th selection variables.
  # Moreover, the i+1th selection variable is enabled. 
  # As there is no difference if a value shall be used as the mth or the nth input of a gate that shall be synthesised
  # (we can just "flip" the semantic of the gate) we say that a node (a PI of the subcircuit or another gate)
  # is the ith input of an gate if the ith selection variable is enabled and k-1 predecessors of the selection variable are enabled.
  def _setupSelectionVariableCounter(self, gate_index) :
    cardinality = self.nof_gate_inputs
    selection_vars = self.selection_variables[gate_index]
    gate_input_vars = self.gate_input_variables[gate_index]
    assert len(selection_vars) > cardinality
    carries = []
    defining_and_gates = [[] for _ in gate_input_vars] # used to define the input variables
    aux = [selection_vars[0]]
    and_var = self._getNewVariable()
    self._writeAnd(and_var, [selection_vars[0], self._getNode(0)])
    defining_and_gates[0].append(and_var)
    for idx, variable in enumerate(selection_vars[1:]) :
      outputs, carry = self._cardinalitySubCircuit(variable, aux, cardinality, False)
      if not carry is None:
        carries += [-carry]
      for i in range(len(aux)) :
        # If we have n selection variables and gates that take k inputs
        # then the n - k + i selection variables is the last one that
        # can be the ith enabled selection variable
        # CHECK:
        if idx > len(selection_vars) - self.nof_gate_inputs + i - 1:
          continue

        and_var = self._getNewVariable()
        self._writeAnd(and_var, [-aux[i], outputs[i], self._getNode(idx + 1)]) # +1 as we loop over selection_vars[1:]
        defining_and_gates[i].append(and_var)

      if len(aux) < len(outputs) :
        and_var = self._getNewVariable()
        self._writeAnd(and_var, [outputs[-1], self._getNode(idx + 1)])
        defining_and_gates[len(outputs) - 1].append(and_var)
      aux = outputs

    constraint_var = self._getNewVariable()
    # if none of the variables in carries is True then not more than cardinality many variables in vars are true
    # if outputs[-1] is true at least cardinality many variables in vars are true
    carries += [outputs[-1]]
    self._writeAnd(constraint_var, carries)
    self.constraintGates += [constraint_var]

    for idx, input_var in enumerate(gate_input_vars) :
      self._writeOr(input_var, defining_and_gates[idx])


  def _getUniversallyQuantifiedVariables(self) :
    return ", ".join(str(x) for x in self.specification.getInputs())


  def _writeGate(self, alias, anded, lines) :
    if anded :
      if len(lines) == 0 :
        self._writeOr(alias, [])
      elif len(lines) == 1 :
        self._writeAnd(alias, lines[0])
      else :
        aux_gate_aliases = []
        for line in lines :
          aux_gate_alias = self._getNewVariable()
          aux_gate_aliases.append(aux_gate_alias)
          self._writeAnd(aux_gate_alias, line)
        self._writeOr(alias, aux_gate_aliases)
    else :
      if len(lines) == 0 :
        self._writeAnd(alias, [])
      elif len(lines) == 1 :
        self._writeOr(alias, lines[0])
      else :
        aux_gate_aliases = []
        for line in lines :
          aux_gate_alias = self._getNewVariable()
          aux_gate_aliases.append(aux_gate_alias)
          self._writeOr(aux_gate_alias, line)
        self._writeAnd(alias, aux_gate_aliases)

  
  # We differentiate between two cases:
  # If inputs are not allowed as outputs we introduce for each gate and each input that is part of a potential cycle a connection variable.
  # If inputs are allowed to be outputs we also introduce connection variables for each input and each input from a potential cycle.
  def _setupConnectionvariables(self) :
    constraint_vars = []
    #if a gate is connected to an input given by self.connection_variables (the keys) then the corresponding connection variable shall be true
    for inp, connection_vars in self.connection_variables.items() :
      input_idx = self.inputs.index(inp)
      if self.config.allowInputsAsOutputs :
        constraint_vars.append(connection_vars[input_idx])
      for i in range(self.nof_gates) :
        if self.config.allowInputsAsOutputs :
          # If we allow inputs as outputs we have to remember that an input may be connected to another input         
          for j, _ in enumerate(self.inputs) :
            constraint_var = self._getNewVariable()
            constraint_vars.append(constraint_var)
            self._writeOr(constraint_var, [-self.selection_variables[i][j], -connection_vars[j],  connection_vars[self._getConnectionVarForGate(i)]])
        
          for j in range(i) :
            constraint_var = self._getNewVariable()
            constraint_vars.append(constraint_var)
            self._writeOr(constraint_var, [-self.selection_variables[i][self._getSelectionVariableIndex(j)], -connection_vars[self._getConnectionVarForGate(j)], connection_vars[self._getConnectionVarForGate(i)]])
        else :
          # The variable is connected: if it is connected to the input or if it is connected to a gate that is connected
          constraint_var = self._getNewVariable()
          constraint_vars.append(constraint_var)
          self._writeOr(constraint_var, [-self.selection_variables[i][input_idx], connection_vars[self._getConnectionVarForGate(i)]])
          for j in range(i) :
            constraint_var = self._getNewVariable()
            constraint_vars.append(constraint_var)
            self._writeOr(constraint_var, [-self.selection_variables[i][self._getSelectionVariableIndex(j)], -connection_vars[self._getConnectionVarForGate(j)], connection_vars[self._getConnectionVarForGate(i)]])

    constraint_var = self._getNewVariable()
    self._writeAnd(constraint_var, constraint_vars)
    self.constraintGates += [constraint_var]

  # If we have multiple pairs, different pairs may form form a cycle together
  # Assume we have two different pairs (x,y) and (a,b) in self.forbidden.
  # It can be the case that x is connected to b and a is connected to y. 
  # To rule out cycles of this kind we make use of the following idea.
  # If (x,y) is in self.forbidden then there is a path from x to y that is not part of the current subcircuit.
  # Now if b is connected to x, this means that y is also connected to b.
  # Thus, all gates that use y as an input are connected to b.
  def _writeCombinedCycleRule(self) :
    assert len(self.forbidden) > 1, "Cycle rules shall only be written if there are forbidden pairs"
    constraint_vars = []
    input_in_pair = {x : set(y for a, y in self.forbidden if a == x) for x in set(x for x,_ in self.forbidden)}
    not_a_pair = {x : set(b for _, b in self.forbidden if not b in y) for x,y in input_in_pair.items()}
    for outp, inputs in not_a_pair.items() :
      output_idx = self.subcircuit_outputs.index(outp)
      for inp in inputs :
        connection_vars = self.connection_variables[inp]
        for i in range(self.nof_gates) :
          for k in input_in_pair[outp] :
            input_idx = self.inputs.index(k)
            if self.config.allowInputsAsOutputs :
              constraint_var = self._getNewVariable()
              constraint_vars.append(constraint_var)
              self._writeOr(constraint_var, [-self.gate_output_variables[i][output_idx], -connection_vars[self._getConnectionVarForGate(i)], connection_vars[input_idx]])
            else :
              condition_var = self._getNewVariable()
              self._writeAnd(condition_var, [self.gate_output_variables[i][output_idx], connection_vars[self._getConnectionVarForGate(i)]])
              for j in range(self.nof_gates) :
                constraint_var = self._getNewVariable()
                constraint_vars.append(constraint_var)
                self._writeOr(constraint_var, [-condition_var, -self.selection_variables[j][input_idx], connection_vars[self._getConnectionVarForGate(j)]])

        if self.config.allowInputsAsOutputs :
          for i, _ in enumerate(self.inputs) :
            for k in input_in_pair[outp] :
              input_idx = self.inputs.index(k)
              constraint_var = self._getNewVariable()
              constraint_vars.append(constraint_var)
              self._writeOr(constraint_var, [-self.gate_output_variables[self.nof_gates + i][output_idx], -connection_vars[i], connection_vars[input_idx]])
                

    constraint_var = self._getNewVariable()
    self._writeAnd(constraint_var, constraint_vars)
    self.constraintGates += [constraint_var]

  def _writeGateOutputCycleConstraints(self) :
    constraint_vars = []
    # For a better readability of the code we first introduce all the clauses restricting the gate variables
    for outp, inp in self.forbidden :
      output_idx = self.subcircuit_outputs.index(outp)
      connection_vars = self.connection_variables[inp]
      for i in range(self.nof_gates) :
        constraint_var = self._getNewVariable()
        constraint_vars.append(constraint_var)
        self._writeOr(constraint_var, [-self.gate_output_variables[i][output_idx], -connection_vars[self._getConnectionVarForGate(i)]]) 
      
      if self.config.allowInputsAsOutputs :
        for i, _ in enumerate(self.inputs) :
          idx = self.nof_gates + i
          constraint_var = self._getNewVariable()
          constraint_vars.append(constraint_var)
          self._writeOr(constraint_var, [-self.gate_output_variables[idx][output_idx], -connection_vars[i]]) 

    constraint_var = self._getNewVariable()
    self._writeAnd(constraint_var, constraint_vars)
    self.constraintGates += [constraint_var]



  def _getBits(self, n, nof_bits) :
    return [n >> i & 1 for i in range(nof_bits - 1, -1, -1)]


 
  # -------------------- symmetry breaking constraints described in SAT-Based Exact Synthesis -------------------- #


  def _addNonTrivialConstraint(self) :
    for i in range(self.nof_gates) :
      # We exclude gates representing constant values
      constraint_constant_false = self._getNewVariable()
      self._writeOr(constraint_constant_false,self.gate_definition_variables[i])
      # Normalised gates cannot represent true
      constraints = [constraint_constant_false]

      # We exclude gates representing the projection of one of its inputs
      for j in range(self.nof_gate_inputs) :
        start = 2 ** (self.nof_gate_inputs - j)
        block_length = 2 ** (self.nof_gate_inputs - j - 1)
        vars1 = [x for k in range(2 ** j) for x in self.gate_definition_variables[i][k * start - (0 if k == 0 else 1): k * start + block_length - 1]]
        vars2 = [-x for k in range(2 ** j) for x in self.gate_definition_variables[i][k * start + block_length - 1: (k + 1) * start - 1]]
        constraint_projection = self._getNewVariable()
        self._writeOr(constraint_projection, vars1 + vars2)
        constraints += [constraint_projection]


      self.constraintGates += constraints

  # Every gate is either an output or an input of another gate
  def _addUseAllStepsConstraint(self):
    for i in range(self.nof_gates) :
      disjuncts = list(self.gate_output_variables[i])
      for j in range(i + 1, self.nof_gates):
        disjuncts += [self.selection_variables[j][self._getSelectionVariableIndex(i)]]
      constraint_var = self._getNewVariable()
      self._writeOr(constraint_var, disjuncts)
      self.constraintGates += [constraint_var]

  #Suppose gate i has inputs i1,...,in and gate j uses i as an input.
  #Then the other n-1 inputs of j shall not be contained in the inputs of i.
  def _addNoReapplicationConstraint(self):
    constraints = []

    for i in range(self.nof_gates) :
      idx_tuple = self._initIndexTuple(self.nof_gate_inputs)
      end_idx_tuple = self._getMaxIdxTuple(self.nof_gate_inputs, self._getSelectionVariableIndex(i))
      while True:
        sel_vars = [-self.selection_variables[i][idx] for idx in idx_tuple]
        for j in range(i + 1, self.nof_gates) :
          selector = self.selection_variables[j][self._getSelectionVariableIndex(i)]
          disjuncts = sel_vars
          disjuncts.append(-selector)
          selection_vars_j = self.selection_variables[j]
          disjuncts += [s for idx, s in enumerate(selection_vars_j) if idx not in idx_tuple and s != selector]

          or_var = self._getNewVariable()
          self._writeOr(or_var, disjuncts)
          constraints.append(or_var)

        if idx_tuple == end_idx_tuple :
          break
        self._incrementIndexTupleSimple(idx_tuple)
    self.constraintGates += constraints

  # If gate g_i depends on gate_j than gate_(i+1) depends on some gate g_k with k>=j
  def _addOrderedStepsConstraint(self) :
    constraints = []
    for i in range(self.nof_gates - 1) :
      for j in range(i) :
        selector = self.selection_variables[i][self._getSelectionVariableIndex(j)]
        vars = [self.selection_variables[i+1][self._getSelectionVariableIndex(k)] for k in range(j, i + 1)]
        constraint_var = self._getNewVariable()
        self._writeOr(constraint_var, [-selector] + vars)
        constraints += [constraint_var]
    self.constraintGates += constraints


  # -------------------- constraints described in SAT-Based Exact Synthesis -------------------- #




  def _writeAnd(self, out_var, inputs) :
    input_str = ", ".join(str(x) for x in inputs)
    self.out.write(str(out_var) + " = and(" + input_str + ")\n")

  def _writeOr(self, out_var, inputs) :
    input_str = ", ".join(str(x) for x in inputs)
    self.out.write(str(out_var) + " = or(" + input_str + ")\n")

  def _writeXor(self, out_var, in1, in2) :
    if self.allow_xors:
      self.out.write(str(out_var) + " = xor(" + str(in1) + ", " + str(in2) + ")\n")
    else:
      or1 = self._getNewVariable()
      self._writeOr(or1, [in1, in2])
      or2 = self._getNewVariable()
      self._writeOr(or2, [-in1, -in2])
      self._writeAnd(out_var, [or1, or2])
  
  def _writeEquivalence(self, out_var, in1, in2) :
    self._writeXor(out_var, -in1, in2)


  def _incrementIndexTupleSimple(self, val) :
    for i in range(len(val)) :
      if i == len(val)-1:
        val[i] += 1
      elif val[i] < val[i+1] - 1:
        val[i] += 1
        break
    return val

  def _resetIndexSubTuple(self, val, idx) :
    for i in range(idx) :
      val[i] = i

  def _incrementIndexTuple(self, val) :
    for i in range(len(val)) :
      if i == len(val)-1:
        val[i] += 1
        self._resetIndexSubTuple(val, i)
      elif val[i] < val[i+1] - 1:
        val[i] += 1
        self._resetIndexSubTuple(val, i)
        break
    return val

  def _initIndexTuple(self, size) :
    return [i for i in range(size)]

  def _getMaxIdxTuple(self, size, max_idx) :
    return [i for i in range(max_idx-size, max_idx)]



  def _addCardinalityConstraint(self, vars, cardinality) :
    if len(vars) == cardinality:
      gate_var = self._getNewVariable()
      self._writeAnd(gate_var, vars)
      self.constraintGates += [gate_var]
      return
    self._SequentialCounterCardinalityConstraint(vars, cardinality)


  # Sequential counter
  # See: https://www.carstensinz.de/papers/CP-2005.pdf
  # The circuit representing the counter for n variables can be split up in 
  # n-1 subcircuits. The ith subcircuit takes the outputs (not the overflow) of
  # the i-1th subcircuit (respectively the first variable if i=1) and the i+1 variable
  # as inputs
  def _SequentialCounterCardinalityConstraint(self, vars, cardinality) :
    assert len(vars) > cardinality
    carries = []
    aux = [vars[0]]
    for idx, variable in enumerate(vars[1:]) :
      last_counter = idx == len(vars) - 2
      outputs, carry = self._cardinalitySubCircuit(variable, aux, cardinality, last_counter)
      aux = outputs
      if not carry is None:
        carries += [-carry]

    constraint_var = self._getNewVariable()
    # if none of the variables in carries is True then not more than cardinality many variables in vars are true
    # if outputs[-1] is true at least cardinality many variables in vars are true
    carries += [outputs[-1]]
    self._writeAnd(constraint_var, carries)
    self.constraintGates += [constraint_var]

  # If last_counter is true only carry and the last output is consider
  def _cardinalitySubCircuit(self, in1, inputs, cardinality, last_counter) :
    if last_counter :
      carry = self._getNewVariable()
      self._writeAnd(carry, [in1, inputs[-1]])
      gate_var_or = self._getNewVariable()
      if len(inputs) == 1 :
        self._writeOr(gate_var_or, [in1, inputs[-1]])
      else :
        gate_var_and = self._getNewVariable()
        self._writeAnd(gate_var_and, [in1, inputs[-2]])
        self._writeOr(gate_var_or, [gate_var_and, inputs[-1]])
      return [gate_var_or], carry

    n = min(len(inputs), cardinality)
    outputs = []
    or_in = in1
    for input in inputs :
      gate_var_or = self._getNewVariable()
      self._writeOr(gate_var_or, [or_in, input])
      outputs += [gate_var_or]

      gate_var_and = self._getNewVariable()
      self._writeAnd(gate_var_and, [in1, input])
      or_in = gate_var_and

    if len(outputs) == cardinality :
      carry = or_in
    else :
      outputs += [or_in] 
      carry = None

    return outputs, carry

  def _writeComment(self, val) :
    if self.writeComments :
      self.out.write("# " + val + "\n")

  def _getNode(self, idx) :
    if idx < len(self.inputs) :
      return self.inputs[idx]
    else :
      return self.internal_gates[idx - len(self.inputs)]

  def _getGate(self, idx) :
    return self.internal_gates[idx]

  def _getGateDefinitionVariable(self, gate_idx, idx) :
    offset = 1 # We use normal gates
    return self.gate_definition_variables[gate_idx][idx - offset]


  def _getTruthConstant(self, idx) :
    if idx == 1:
      return self.true
    else :
      return self.false
    
  def _getNewVariable(self) :
    self.last_used_variable += 1
    return self.last_used_variable

  def _getSelectionVariableIndex(self, gate_idx) :
    return len(self.inputs) + gate_idx

  def _getConnectionVarForGate(self, gate_idx) :
    if self.config.allowInputsAsOutputs :
      return len(self.inputs) + gate_idx
    else :
      return gate_idx