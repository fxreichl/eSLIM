import time
import sys
import logging

import heapq

import bitarray
import bitarray.util

import copy

import utils
from utils import Configuration
from utils import isNormalised
from utils import getBitSeq
from utils import getAllIndices

class Gate :
  
  def __init__(self, gate_alias, inputs, table) :
    self.gate_alias = gate_alias
    self.inputs = inputs
    # Possibly pass a "normal" list and generate a bitarray by bitarray.bitarray(inputs)
    self.table = table

  # renaming[x] = None indicates that x is a constant (false) gate
  def substitute(self, renaming) :
    removed = [idx for idx, x in enumerate(self.inputs) if x in renaming and renaming[x] is None]
    # Even if the gate is reduced to the constant gate we new the renamed inputs to update the gate outputs
    renamed_inputs = [renaming[x] if x in renaming else x for x in self.inputs if not x in renaming or not renaming[x] is None]
    if len(removed) > 0 :
      self._reduceTable(removed)
    if len(self.inputs) > 0 : 
      self.inputs = renamed_inputs
    return renamed_inputs

  def _reduceTable(self, to_remove) :
    for idx in to_remove :
      reversed_idx = len(self.inputs) - 1 - idx
      self.table = bitarray.bitarray(x for idx, x in enumerate(self.table) if idx % (2 ** (reversed_idx + 1)) < (2 ** (reversed_idx)))
    if not self.table.any() : # the table representing the constant false
      self.inputs = []
      self.table = bitarray.util.zeros(1)

  def isConstant(self) :
    return len(self.inputs) == 0

  # If the gate is a projection to one of its inputs, the index of the respective input is returned
  # Only apply if the gate is not constant
  # If gates can have more than two inputs: Only sufficient but not a necessary condition
  def projectionOn(self) :
    # A normal gate with one inputs represents either the constant false or the projection to its inputs
    if len(self.inputs) == 1 :
      return 0
    return None


  def getAlias(self) :
    return self.gate_alias

  # names: use the given inputs instead of self.inputs
  def getQCIRGates(self, names = None) :
    assert names is None or len(names) == len(self.inputs)
    input_names = self.inputs if names is None else names
    # If the gate is false for the majority of the input combinations we
    # represent the gate by a disjunction of conjunctions, otherwise by
    # a conjunction of disjunctions.
    anded = len([x for x in self.table if x > 0]) <= (2 ** (len(self.inputs) - 1))
    val = 1 if anded else 0
    lines = []
    for idx, tt_val in enumerate(self.table) :
      if tt_val == val :
        line = [input_names[i] if v == val else -input_names[i] for i,v in enumerate(getBitSeq(idx, len(self.inputs)))]
        lines.append(line)
    return (anded, lines)

  # names: use the given inputs instead of self.inputs
  def traverseTable(self, names = None) :
    assert names is None or len(names) == len(self.inputs)
    input_names = self.inputs if names is None else names
    for idx, tt_val in enumerate(self.table) : 
      inputs = [input_names[i] if v == 1 else -input_names[i] for i,v in enumerate(getBitSeq(idx, len(self.inputs)))]
      yield (inputs, tt_val)

class Specification :

  def __init__(self, pis, pos) :
    self.config = Configuration()
    self.pis = pis
    self.pis_set = set(pis)
    self.pos = pos
    self.pos_set = set(self.pos)
    self.max_var = max(pis) # non pi outputs need to be introduced later
    # As we use bitarray anywhere we can replace the boolean array
    self.negated_pos = bitarray.util.zeros(len(pos))

    self.constant_gate_alias = None

    # Map the gate aliases to tuples (level, outputs, gate) 
    self.alias2gate = {}
    self.alias2outputs = {x : set() for x in self.pis}
    self.alias2level = {x : 0 for x in self.pis}

    self.topological_order = None
    self.joining_gates = set()

  def setConfig(self, config : Configuration) :
    self.config = config

  def orderedGateTraversal(self) :
    # The constant gate is in alias2gate
    # if not self.constant_gate_alias is None :
    #   yield self.alias2gate[self.constant_gate_alias]
    for x in self.topological_order :
      yield self.alias2gate[x]

  def gateTraversal(self) :
    # The constant gate is in alias2gate
    # if not self.constant_gate_alias is None :
    #   yield self.alias2gate[self.constant_gate_alias]
    for _, gate in self.alias2gate.items() :
      yield gate

  def getGateAliases(self) :
    return list(self.alias2gate.keys())

  def getGateAliasesSet(self) :
    return set(self.alias2gate.keys())
  
  def getRejoiningGates(self) :
    return self.joining_gates

  def getNofGates(self) :
    return len(self.alias2gate)

  def getGate(self, alias) :
    # assert alias in self.alias2gate, f"Alias {alias} not contained in {self.alias2gate.keys()}"
    return self.alias2gate[alias]

  def getGateInputs(self, alias) :
    assert alias in self.alias2gate, f"The alias: {alias} does not describe a gate"
    return self.alias2gate[alias].inputs

  def getGateOutputs(self, alias) :
    assert alias in self.alias2outputs, f"The alias: {alias} does not describe a gate"
    return self.alias2outputs[alias]

  def getGateLevel(self, alias) :
    return self.alias2level[alias]

  def getInputs(self) :
    return self.pis

  def getOutputs(self) :
    return self.pos

  def getMaxAlias(self) :
    return self.max_var

  def isOutputNegated(self, idx) :
    return self.negated_pos[idx]

  def isPO(self, alias) :
    return alias in self.pos_set
  
  def isPI(self, alias) :
    return alias in self.pis_set

  def getDepth(self) :
    return max(self.alias2level[x] for x in self.pos)

  def getGatesAtLevel(self, level) :
    gates = set()
    for alias, lv in self.alias2level.items() :
      if lv == level :
        gates.add(alias)
    return gates

  def getSubcircuitInputs(self, aliases) :
    input_set = set(x for y in aliases for x in self.getGateInputs(y))
    input_set.difference_update(aliases)
    return input_set

  def getSubcircuitFirstLevel(self, aliases) :
    alias_set = set(aliases)
    return set(x for x in aliases if not self.getGateInputs(x).issubset(alias_set))

  def getDirectSuccessors(self, aliases) :
    successor_set = set(x for y in aliases for x in self.getGateOutputs(y))
    successor_set.difference_update(aliases)
    return successor_set

  def getSubcircuitOutputs(self, aliases) :
    alias_set = set(aliases)
    output_set = set(x for x in aliases if self.isPO(x) or not self.getGateOutputs(x).issubset(alias_set))
    return output_set

  def getGatesWithSuccessor(self, aliases) :
    alias_set = set(aliases)
    output_set = set(x for x in aliases if not self.getGateOutputs(x).issubset(alias_set))
    return output_set

  # transitive fanin cone
  def getTFI(self, aliases) :
    pis_set = set(self.pis)
    to_consider = set(aliases)
    tfi = set()
    while len(to_consider) > 0 :
      x = to_consider.pop()
      tfi.add(x)
      to_consider.update(y for y in self.getGateInputs(x) if y not in pis_set and y not in tfi)
    return tfi

  def getTFISubcircuit(self, aliases, subcircuit) :
    pis_set = set(self.pis)
    to_consider = set(aliases)
    tfi = set()
    while len(to_consider) > 0 :
      x = to_consider.pop()
      tfi.add(x)
      to_consider.update(y for y in self.getGateInputs(x) if y not in pis_set and y not in tfi and y in subcircuit)
    return tfi

  # transitive fanout cone
  # unlike to getTFI aliases is not contained in the result (unless an element of aliases is a successor of another element)
  def getTFO(self, aliases) :
    to_consider = {y for x in aliases for y in self.getGateOutputs(x)}
    tfo = set()
    while len(to_consider) > 0 :
      x = to_consider.pop()
      tfo.add(x)
      # to_consider.update(y for y in self.getGateOutputs(x) if y not in self.pos_set and y not in tfo)
      to_consider.update(y for y in self.getGateOutputs(x) if y not in tfo)
    return tfo

  def getTFOSubcircuit(self, aliases, subcircuit) :
    to_consider = {y for x in aliases for y in self.getGateOutputs(x)}
    tfo = set()
    while len(to_consider) > 0 :
      x = to_consider.pop()
      tfo.add(x)
      # to_consider.update(y for y in self.getGateOutputs(x) if y not in self.pos_set and y not in tfo and y in subcircuit)
      to_consider.update(y for y in self.getGateOutputs(x) if y not in tfo and y in subcircuit)
    return tfo
  

  def _getConnected(self, alias, gates, internal_gates) :
    level = min(self.alias2level[x] for x in gates)
    connected_pairs = []
    # The level of each element of gates is larger then the level of gates_var, thus there cannot be a connected pair
    if level >= self.alias2level[alias] :
      return connected_pairs
    to_check = [alias]
    seen = set(internal_gates) # internal gates shall be ignored. We are only interested in paths outside of the subcircuit.
    while len(to_check) > 0:
      current_gate = to_check.pop()
      seen.add(current_gate)
      for inp in self.getGateInputs(current_gate) :
        if inp in gates :
          connected_pairs.append((inp, alias))
        elif not inp in seen :
          seen.add(inp)
          inp_level = self.alias2level[inp]
          if inp_level > level :
            to_check.append(inp)
    return connected_pairs


  def cycleExpansion(self, aliases, stop_at) :
    pis_set = set(self.pis)
    to_consider = set(aliases)
    tfi = set()
    while len(to_consider) > 0 :
      x = to_consider.pop()
      tfi.add(x)
      if x in stop_at :
        continue
      to_consider.update(y for y in self.getGateInputs(x) if y not in pis_set and y not in tfi)
    return tfi

  # TODO: rework
  # computes a list of pairs whose first element is an output and whose second element is an input.
  # if the list contains a pair (a,b) then the input b depends on the output a
  def getPotentialCycles(self, inputs, outputs, internal_gates) :
    cycle_candidates = []
    if len(inputs) == 0 :
      logging.warning(f"Warning -- getPotentialCycles: inputs empty")
    if len(outputs) == 0 :
      logging.warning(f"Warning -- getPotentialCycles: outputs empty")
      return cycle_candidates
    
    # Only inputs which are successors of outputs and outputs which are predecessors of inputs need to be considered in the connection check
    tfo = self.getTFO(outputs)
    inputs_to_consider = tfo.intersection(set(inputs))
    if len(inputs_to_consider) == 0 :
      return cycle_candidates
    # tfi = self.getTFI(inputs_to_consider)
    tfi = self.cycleExpansion(inputs_to_consider, internal_gates)
    ouputs_to_consider = tfi.intersection(set(outputs))

    # for inp in inputs :
    #   cycle_candidates += self._getConnected(inp, outputs, internal_gates)
    # return cycle_candidates

    if len(inputs_to_consider) == 1 :
      input = next(iter(inputs_to_consider))
      cycle_candidates = [(x, input) for x in ouputs_to_consider]
    elif len(ouputs_to_consider) == 1 :
      output = next(iter(ouputs_to_consider))
      cycle_candidates = [(output, x) for x in inputs_to_consider]
    else :
      for inp in inputs_to_consider :
        cycle_candidates += self._getConnected(inp, ouputs_to_consider, internal_gates)

    return cycle_candidates

  # Expand all successors of outputs with a level < max input level.
  # Annotate each expanded gate with the outputs it depends on.
  # If an input gets annotated, then it depends on an output which 
  # means that there is a potential cycle.
  # Expand the gates by using a priority queue, where gates with the smallest
  # level are selected first.
  # If a gate is expanded, add its annotations to its successors.
  def getPotentialCyclesMk2(self, inputs, outputs, internal_gates) :
    cycle_candidates = []
    if len(inputs) == 0 :
      logging.warning(f"Warning -- getPotentialCycles: inputs empty")
    if len(outputs) == 0 :
      logging.warning(f"Warning -- getPotentialCycles: outputs empty")
      return cycle_candidates

    gates_to_consider = [(self.getGateLevel(x), x) for x in outputs]
    min_out_level = min(self.getGateLevel(x) for x in outputs)
    max_in_level = max(self.getGateLevel(x) for x in inputs)
    heapq.heapify(gates_to_consider)
    current_level = gates_to_consider[0][0]
    annotation_dict = {x : {x} for x in outputs}
    while len(gates_to_consider) > 0 and current_level < max_in_level :
      current_level, alias = heapq.heappop(gates_to_consider)
      for x in self.getGateOutputs(alias) :
        if x in annotation_dict :
          annotation_dict[x].update(annotation_dict[alias])
        else :
          if x in internal_gates :
            continue
          annotation_dict[x] = annotation_dict[alias]
          heapq.heappush(gates_to_consider, (self.getGateLevel(x), x))

    for x in inputs :
      if x in annotation_dict :
        for y in annotation_dict[x] :
          cycle_candidates.append((x, y))
    return cycle_candidates
        


  def removeGate(self, alias) :
    self.removeGateAux(alias, self.getGateInputs(alias))

  # If we rename inputs, it is possible that inputs are removed.
  # But we want to process all old inputs
  def removeGateAux(self, alias, inputs) :
    assert alias in self.alias2gate
    for x in inputs :
      if x in self.alias2outputs : # if the input was already removed, it is not part of the dict
        self.alias2outputs[x].discard(alias)
    del self.alias2gate[alias]
    del self.alias2level[alias]
    del self.alias2outputs[alias]

  def insertGates(self, new_gates) :
    # To avoid errors if new_gates are not topologically ordered
    # self.alias2outputs.update({x[0] : set() for x in new_gates})
    for g in new_gates :
      alias, inputs, table = g
      self.addGate(alias, inputs, table)


  def updatePos(self, output_assoc) :
    self.pos = [(self.getConstantAlias(x) if output_assoc[x] is None else output_assoc[x]) if x in output_assoc else x for x in self.pos]
    self.pos_set = set(self.pos)


  # As in a normalised circuit there is only one possibility for a constant gate
  # We only use a single representation
  def getConstantAlias(self, candidate) :
    if self.constant_gate_alias is None :
      self.constant_gate_alias = candidate
      self.alias2level[candidate] = 0
      self.alias2outputs[candidate] = set()
      gate = Gate(candidate, [], bitarray.util.zeros(1))
      self.alias2gate[candidate] = gate
    return self.constant_gate_alias
  
  def hasConstantOutput(self) :
    return self.constant_gate_alias is not None

  def removeUnusedGates(self, aliases_to_check) :
    unused = set()
    while len(aliases_to_check) > 0 :
      x = aliases_to_check.pop()
      # if x not in self.alias2outputs :
      #   raise utils.ViolatedInvariantException(f"Unused check: alias {x} not in output dict")
      if not self.isPO(x) and len(self.getGateOutputs(x)) == 0 : # the gate is not used
        aliases_to_check.update(self.getGateInputs(x))
        aliases_to_check.difference_update(self.pis)
        self.removeGate(x)
        unused.add(x)
    return unused

  # Get the successors of the subcircuit outputs
  def getOutputsDict(self, to_remove, output_assoc) :
    subcircuit_outputs = self.getSubcircuitOutputs(to_remove)
    to_remove_set = set(to_remove)
    log = {}
    for x in subcircuit_outputs :
      outputs = self.getGateOutputs(x)
      outputs.difference_update(to_remove_set)
      # The constant gate is substituted. We only use the constant gate to represent constant pos.
      if output_assoc[x] is None :
        continue
      if output_assoc[x] in log :
        log[output_assoc[x]].update(outputs)
      else :
        log[output_assoc[x]] = outputs
    return log

  def incorportateOutputs(self, output_log) :
    for alias, outputs in output_log.items() :
      self.alias2outputs[alias].update(outputs)


  # Ensure that the constant gate is not replaced
  # If the internal constant gate is part of to_remove this will cause an error
  # new_gates must be sorted
  # If a gate is reduced because of constant inputs it is
  # possible that the reduced gate is the projection to one of its inputs
  # Such gates shall be remove by suitable substitutions.
  def replaceSubcircuit(self, to_remove, new_gates, output_assoc) :
    if self.config.debug :
      self.old_specification = copy(self)
    old_gate_aliases = set(x for x in to_remove)
    successors_to_update = self.getDirectSuccessors(old_gate_aliases)
    unused_gate_candidates = self.getSubcircuitInputs(old_gate_aliases)
    subcircuit_output_dict = self.getOutputsDict(to_remove, output_assoc)
    redundant = set()
    for x in to_remove :
      self.removeGate(x)
    self.insertGates(new_gates)
    self.incorportateOutputs(subcircuit_output_dict)
    # We may need to consider a gate again. In this case we need to know that it was already renamed
    renamed = set()
    aux_dict = {}
    while len(successors_to_update) > 0 :
      alias_to_process = successors_to_update.pop()
      gate = self.getGate(alias_to_process)
      if alias_to_process in renamed :
        renamed_unpruned_inputs = gate.substitute(aux_dict)
      else :
        renamed_unpruned_inputs = gate.substitute(output_assoc)
      renamed.add(alias_to_process)
      if gate.isConstant() :
        output_assoc[alias_to_process] = None
        aux_dict[alias_to_process] = None
        # TODO: the gate may already be processed
        successors_to_update.update(self.getGateOutputs(alias_to_process))
        redundant.add(alias_to_process)
        self.removeGateAux(alias_to_process, renamed_unpruned_inputs)
        unused_gate_candidates.update(renamed_unpruned_inputs)
        # An input of the subcircuit may become constant after backwards propagation.
        # In this case there is no need to check the gate is unused.
        unused_gate_candidates.discard(alias_to_process)

    self.updatePos(output_assoc)
    unused_gate_candidates.difference_update(self.pis)
    unused = self.removeUnusedGates(unused_gate_candidates)
    unused.update(redundant)
    self.setGateLevels()
    return unused


  def init(self, ordered_gate = True) :
    if not ordered_gate :
      self.setGateOutputs()
    self.removeRedundant()
    self.removeConstantGates()
    self.setGateLevels()




  def setGateLevels(self) :
    self.alias2level = {x : 0 for x in self.pis}
    if self.constant_gate_alias is not None :
      self.alias2level[self.constant_gate_alias] = 0
    self.getTopologicalOrder()
    for x in self.topological_order :
      if len(self.getGateInputs(x)) > 0 :
        self.alias2level[x] = 1 + max(self.alias2level[y] for y in self.getGateInputs(x))
      # else the gate is a constant gate which has level 0

  # After setting up the specification we want to use the invariant that each gate has at least one input.
  # With the exception of a special constant gate that may only be used as a PO but not as an input for 
  # other gates

  def removeConstantGates(self) :
    constant_gates = {x for x in self.getGateAliases() if len(self.getGateInputs(x)) == 0}
    substitution = {x : None for x in constant_gates}
    while constant_gates :
      alias = constant_gates.pop()
      for x in self.getGateOutputs(alias) :
        gate = self.getGate(x)
        gate.substitute(substitution)
        if gate.isConstant() :
          constant_gates.add(x)
          substitution[x] = None
      self.removeGate(alias)
      if self.isPO(alias) :
        constant_alias = self.getConstantAlias(alias)
        for out_idx in getAllIndices(self.pos, alias) :
          # out_idx = self.pos.index(alias)
          self.pos[out_idx] = constant_alias
          self.pos_set = set(self.pos)
      


  # More Python friendly style of sorting the aliases
  # Replace the recursion by an iteration
  def getTopologicalOrder(self) :
    self.joining_gates.clear()
    expanded = set()
    visited = set() # Only used for a debug check
    # Only needed for computing rejoining gates
    # Every gate that can be reached by at least two possible paths from a PI is added
    successors_current_pi = set()
    self.topological_order = [None] * len(self.alias2gate)
    order_index = len(self.topological_order) - 1
    # The pis shall be treated differently as the gates
    # Thus, we do not put them into the stack and handle them all at once
    for pi in self.pis :
      # There are two kinds of entries on the stack
      # alias, False -> add the children to the stack
      # alias, True  -> all children processed -> insert into ordering
      to_process_stack = []
      successors_current_pi.clear()
      for x in self.alias2outputs[pi] :
        if x not in expanded :
          to_process_stack.append((x, False))
      while len(to_process_stack) > 0 :
        alias, children_processed = to_process_stack.pop()
        if self.config.compute_joining_gates :
          successors_current_pi.add(alias)
        if alias in expanded :
          assert not children_processed
          continue
        if children_processed :
          self.topological_order[order_index] = alias
          order_index -= 1
          expanded.add(alias)
        else :
          # We try to expand a gate that is already on the current DFS path.
          if alias in visited :
            raise utils.ViolatedInvariantException(f"Insertion of subcircuit caused a cycle in the circuit - alias: {alias}", True)
            # assert False, "Cycle detected"
          # Will get processed as soon as all outputs are processed
          to_process_stack.append((alias, True))
          visited.add(alias)
          for x in self.alias2outputs[alias] :
            if x not in expanded :
              to_process_stack.append((x, False))
            if self.config.compute_joining_gates and x in successors_current_pi :
              self.joining_gates.add(x)

    # The constant gate is not connected to the pis. Thus it needs to be handled separately.
    if len(expanded) != len(self.alias2gate) :
      # The constant gate is not expanded. Thus, it may not occur in the expansion. 
      # If the set of all gates and the set of expanded gates differ in gates other than the constant gate
      # this means that there are gates that are not used by any PO.
      # As gates that are not used, are supposed to be removed this indicates an error in the program.
      if len(expanded) < len(self.alias2gate) :
        if len(expanded) != len(self.alias2gate) - 1 or self.constant_gate_alias is None :
          all_gates = set(self.alias2gate)
          diff_set = all_gates.difference(expanded)
          for x in diff_set :
            print(f"Gate: {x}; inputs: {self.getGateInputs(x)}; outputs: {self.getGateOutputs(x)}")
            print(f"Inputs of successors of {x}")
            for y in self.getGateOutputs(x) :
              print(f"Gate: {y}; inputs: {self.getGateInputs(y)}")
      # END:
      assert len(expanded) == len(self.alias2gate) - 1, f"Topological ordering detected components that are not connected to a PO -- lengths: {len(expanded)}; {len(self.alias2gate)}"
      assert self.constant_gate_alias is not None, "Topological ordering detected components that are not connected to a PO"
      self.topological_order[0] = self.constant_gate_alias


  # table: A bitarray
  # All input gates must already be present in the specification
  def addGate(self, gate_alias, inputs, table) :
    assert isinstance(table, bitarray.bitarray)
    self.max_var = max(self.max_var, gate_alias)
    assert len(table) == 2 ** len(inputs), f"Table has length: {len(table)}; inputs: {inputs}; table:  {table}"
    assert isNormalised(table)
    for x in inputs :
      self.alias2outputs[x].add(gate_alias)
    self.alias2gate[gate_alias] = Gate(gate_alias, inputs, table)
    self.alias2outputs[gate_alias] = set()
    self.alias2level[gate_alias] = None

  # Does not require that all input gates are part of the specification.
  # As the input gates are not necessarily available the outputs of the inputs cannot be set.
  def addGateUnsorted(self, gate_alias, inputs, table) :
    assert isinstance(table, bitarray.bitarray)
    self.max_var = max(self.max_var, gate_alias)
    assert len(table) == 2 ** len(inputs)
    assert isNormalised(table)
    self.alias2gate[gate_alias] = Gate(gate_alias, inputs, table)
    self.alias2outputs[gate_alias] = set()
    self.alias2level[gate_alias] = None

  def setGateOutputs(self) :
    pis_set = set(self.pis)
    # A PI may be an PO
    to_process = [x for x in self.pos if x not in pis_set]
    seen = set(to_process)
    while len(to_process) > 0 :
      alias = to_process.pop()
      for x in self.getGate(alias).inputs :
        self.alias2outputs[x].add(alias)
        if not x in seen and not x in pis_set:
          seen.add(x)
          to_process.append(x)
            
  def removeRedundant(self) :
    to_process = set()
    for alias, outputs in self.alias2outputs.items() :
      if len(outputs) == 0 and alias not in self.pis_set and alias not in self.pos_set :
        to_process.add(alias)
    self.removeUnusedGates(to_process)


  # TODO: An alias may represent more than one output
  # By using index not necessarily the correct output gets negated
  def negateOutput(self, alias) :
    # one gate may represent more than one output
    for i in getAllIndices(self.pos, alias) :
      self.negated_pos[i] = 1

    # index = self.pos.index(alias)
    # self.negated_pos[index] = 1
  
  def toggleOutputNegation(self, alias) :
    # one gate may represent more than one output
    for i in getAllIndices(self.pos, alias) :
      self.negated_pos[i] = 1 - self.negated_pos[i]

    # index = self.pos.index(alias)
    # self.negated_pos[index] = 1 - self.negated_pos[index]


  def getOutputsToNegate(self) :
    positive_outputs = set()
    negative_outputs = set()
    for idx, out in enumerate(self.pos) :
      if self.negated_pos[idx] :
        negative_outputs.add(out)
      else :
        positive_outputs.add(out)
    outputs_in_both_polarities = positive_outputs.intersection(negative_outputs)
    negative_outputs.difference_update(positive_outputs)
    return negative_outputs, outputs_in_both_polarities