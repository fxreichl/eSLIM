import random
import time
import logging


from subcircuitSynthesiser import SubcircuitSynthesiser
from utils import Configuration
from utils import mean
from utils import chooseFromSet

from specification import Specification

import aigerIO
import blifIO


class Synthesiser :
    
  @staticmethod
  def getSpecification(spec, ordered_inputs = False) :
    if spec.endswith(".aig") or spec.endswith(".aag") :
      return aigerIO.getSpecification(spec)
    else :
      assert spec.endswith(".blif")
      return blifIO.getSpecification(spec, ordered_inputs)

  @staticmethod
  def getSynthesiser(spec, config : Configuration, ordered_inputs = False) :
    specification = Synthesiser.getSpecification(spec, ordered_inputs)
    return Synthesiser(specification, config)
  
  def reduce(self, budget, subcircuit_size) :
    self.traverser.subcircuit_size = subcircuit_size
    initial_nof_gates = self.specification.getNofGates()
    available_time, available_iterations = budget
    self.total_available_time = available_time
    self._traverseGates(available_iterations)
    final_nof_gates = self.specification.getNofGates()
    logging.info(f"Initial #gates: {initial_nof_gates}; Final #gates: {final_nof_gates}")
    return self

  def writeSpecification(self, fname, writeBlif=True) :
    if writeBlif :
      blifIO.writeSpecification(fname, self.specification)
    else :
      aigerIO.writeSpecification(fname, self.specification)
  

  # Use getSynthesiser instead
  # forbidden_pairs: collection of pairs (a,b) where a is an output of the circuit
  # and b is a set of inputs of the circuits. 
  # In the computed circuit a must not depend on inputs in b.
  # The caller is responsible for ensuring that such a circuit exists
  # (e.g. by checking if the initial circuit has this property).
  def __init__(self, spec : Specification, config : Configuration, forbidden_pairs = [], termination_event = None) :
    self.specification = spec
    config.validateConfig()
    self.config = config
    self.termination_event = termination_event
    self.synthesiser = SubcircuitSynthesiser(self.specification, config)
    self._setup()
    
    # If the QBF calls yielding SAT are very fast increase the size of the considered subcircuits
    self.subcircuit_size_validated = False
    self.check_for_larger_subcircuits = not config.fixed_subcircuit_size
    self.last_validated = None
    self.nof_validation_trials = 0

    self.replacements_single_output_subcircuits = 0
    self.reduction_single_output_subcircuits = 0
    self.replacements_multi_output_subcircuits = 0
    self.reduction_multi_output_subcircuits = 0

    self.intermediate_counter = 0 # Auxiliary counter used just for logging

    self.dependency_constraints = []
    for out, inputs in forbidden_pairs :
      tfi = set(self.specification.getTFI({out}))
      tfo = set(self.specification.getTFO(inputs))
      self.dependency_constraints.append([out, inputs, tfi, tfo])

  def _setup(self) :
    forward_search = self.config.search_direction_forward
    if self.config.root_selection_strategy == self.config.RootSelectionStrategy.reconvergenceBased :
      forward_search = False
    if self.config.search_strategy == self.config.SearchStrategy.exhaustiveBFS :
      self.expander = BFSExpansion(self.specification, self.config, forward_search)
    elif self.config.search_strategy == self.config.SearchStrategy.nonExhaustiveBFS :
      self.expander = RandomizedBFS(self.specification, self.config, forward_search)
    elif self.config.search_strategy == self.config.SearchStrategy.inputReduction :
      self.expander = InputMinimization(self.specification, self.config, forward_search)
    elif self.config.search_strategy == self.config.SearchStrategy.outputReduction :
      self.expander = OutputMinimization(self.specification, self.config, forward_search)
    elif self.config.search_strategy == self.config.SearchStrategy.singleOutputSubcircuit :
      self.expander = SingleOutput(self.specification, self.config)
    else :
      assert False, f"Invalid expansion strategy: {self.config.search_strategy}"

    if self.config.root_selection_strategy == self.config.RootSelectionStrategy.random :
      self.traverser = RandomizedTraversal(self.specification, self.expander, self.config)
    elif self.config.root_selection_strategy == self.config.RootSelectionStrategy.reconvergenceBased :
      self.traverser = ReconvergentTraversal(self.specification, self.expander, self.config)
    elif self.config.root_selection_strategy == self.config.RootSelectionStrategy.completeCoverage :
      self.traverser = CompleteCoverage(self.specification, self.expander, self.config)
    else :
      assert False, f"Invalid root selection strategy: {self.config.root_selection_strategy}"

  def _traverseGates(self, available_iterations) :
    check_budget = available_iterations is not None
    counter = 0
    self.start = time.time()
    while True :
      if check_budget and counter >= available_iterations :
        logging.info(f"Available iterations used up. Nof considered subcircuits: {counter}")
        return
      if not self._checkTime() :
        logging.info(f"Available time used up. Nof considered subcircuits: {counter}")
        return
      if self.termination_event is not None and self.termination_event.is_set() :
        logging.info(f"Termination event set. Nof considered subcircuits: {counter}")
        return
      if self.config._single_improvement and self.synthesiser.logger.nof_reduced > 0 :
        logging.info(f"Terminate as reduction was found. Nof considered subcircuits: {counter}")
        return
      if self.specification.getNofGates() == 0 :
        logging.info("No Gates in specification")
        return
      subcir_data = self.traverser.getSubcircuit()
      if subcir_data is None :
        return
      root_gate, to_replace = subcir_data
      synth_res = self._replaceSubcircuit(to_replace, self.config.gate_size)
      self.traverser.update(to_replace, synth_res)
      replaceable, subcir_data, timeout = synth_res
      if replaceable :
        counter += 1
      if not self._updateSubcircuitSize(to_replace, synth_res, counter) :
        return
      self._logging(root_gate, to_replace, synth_res, counter)
      

  # returns falls if size could not be updated
  def _updateSubcircuitSize(self, to_replace, synth_res, counter) :
    replaceable, subcir_data, timeout = synth_res
    if not self.subcircuit_size_validated :
      if timeout :
        self.nof_validation_trials += 1
        if self.nof_validation_trials >= self.config.subcircuit_size_validation_number :
          if self.last_validated is None :
            self.traverser.subcircuit_size -= 1
            self.nof_validation_trials = 0
            if self.traverser.subcircuit_size < 2 :
              logging.warn("The encoding for a subcircuit with 2 gates could not be solved by the QBF solver within the given timeout.")
              logging.warn("Restart with a longer timeout -- be aware if the given timeout was already reasonably long then maybe the specification is too hard.")
              return False
          else :
            self.traverser.subcircuit_size = self.last_validated
            self.subcircuit_size_validated = True
          self.check_for_larger_subcircuits = False
          logging.info(f"QBF call takes too long -- decrease the subcircuit size to: {self.traverser.subcircuit_size}")
        elif replaceable :
          self.last_validated = self.traverser.subcircuit_size
          if self.traverser.subcircuit_size == len(to_replace) :
            self.subcircuit_size_validated = True
      
    if self.check_for_larger_subcircuits and counter % self.config.check_subcircuit_size_interval == 0 :
      if self.traverser.subcircuit_size in self.synthesiser.timer.recorded_timings_sat and len(self.synthesiser.timer.recorded_timings_sat[self.traverser.subcircuit_size]) > self.config.subcircuit_size_increase_nof_samples :
        if mean(self.synthesiser.timer.recorded_timings_sat[self.traverser.subcircuit_size]) < self.config.subcircuit_size_increase_limit :
          self.traverser.subcircuit_size += 1
          self.nof_validation_trials = 0
          self.subcircuit_size_validated = False
          logging.info(f"QBF call fast -- increase the subcircuit size to {self.traverser.subcircuit_size}")

    return True


  def _logging(self, root_gate, to_replace,  synth_res, counter) :
    log_spec_time_steps = self.config.log_time_steps is not None and self.config.specification_log_dir is not None
    log_spec_iteration_steps = self.config.log_iteration_steps is not None and self.config.specification_log_dir is not None
    replaceable, subcir_data, timeout = synth_res

    if self.config.gate_count_trace :
      logging.info(f"iteration: {counter}; root gate: {root_gate}; old-size: {len(to_replace)}; new-size: {len(subcir_data[0]) if replaceable  else '-'}; to replace: {to_replace}")
    else :
      logging.debug(f"iteration: {counter}; root gate: {root_gate}; old-size: {len(to_replace)}; new-size: {len(subcir_data[0]) if replaceable  else '-'}; to replace: {to_replace}")

    if (log_spec_time_steps and int(self._getEllapsedTime() // self.config.log_time_steps) > self.intermediate_counter) :
      fname = f"{self.config.specification_log_dir}/spec_it_{counter}.blif"
      self.writeSpecification(fname)
      logging.info(f"Intermediate Results: {int(self._getEllapsedTime() // self.config.log_time_steps)} {self._getEllapsedTime()}")
      self.intermediate_counter += 1
    # Log intermediate results
    elif log_spec_iteration_steps and counter % self.config.log_iteration_steps == 0 :
      fname = f"{self.config.specification_log_dir}/spec_it_{counter}.blif"
      self.writeSpecification(fname)

    if replaceable :
        gate_names, output_assoc, unused = subcir_data
        reduced = len(gate_names) < len(to_replace)
        if len(output_assoc) == 1 :
          self.replacements_single_output_subcircuits += 1
          if reduced :
            self.reduction_single_output_subcircuits += 1
        else :
          self.replacements_multi_output_subcircuits += 1
          if reduced :
            self.reduction_multi_output_subcircuits += 1

    logging.debug(f"Iteration: {counter}; Nof Gates: {self.specification.getNofGates()}")
      



  def _replaceSubcircuit(self, to_replace, nof_inputs) :
    require_reduction = self.config.require_reduction and not self.subcircuit_size_validated
    dependency_constraints_present = len(self.dependency_constraints) > 0
    if dependency_constraints_present :
      subcircuit_inputs = self.specification.getSubcircuitInputs(to_replace)
      subcircuit_outputs = self.specification.getSubcircuitOutputs(to_replace)
    val = self.synthesiser.reduce(to_replace, nof_inputs, self.config.require_reduction, self.dependency_constraints)
    if len(self.dependency_constraints) > 0 :
      replaceable, subcir_data, _ = val
      _, output_assoc, _ = subcir_data
      if replaceable :
        for idx, (inputs, out, tfi, tfo) in enumerate(self.dependency_constraints) : 
          tfi_output_intersection = tfi.intersection(subcircuit_outputs)
          tfi_output_intersection_renamed = set(output_assoc[x] for x in tfi_output_intersection)
          tfi_output_intersection_old = tfi.intersection(subcircuit_outputs)
          tfi_output_intersection_new = self.specification.getTFISubcircuit(tfi_output_intersection_renamed, to_replace)
          tfi.difference_update(self.specification.getTFI(tfi_output_intersection_old.difference(tfi_output_intersection_new)))
          tfi.update(self.specification.getTFI(tfi_output_intersection_new.intersection(tfi_output_intersection_old)))

          tfo_input_intersection = tfo.intersection(subcircuit_inputs)
          tfo_output_intersection_old = set(output_assoc[x] for x in tfo.intersection(subcircuit_outputs))
          tfo_output_intersection_new = self.specification.getTFOSubcircuit(tfo_input_intersection, to_replace)
          tfo.difference_update(self.specification.getTFO(tfo_output_intersection_old.difference(tfo_output_intersection_new)))
          tfo.update(self.specification.getTFO(tfo_output_intersection_new.difference(tfo_output_intersection_old)))

          if out in output_assoc :
            out = output_assoc[out]
          self.dependency_constraints[idx] = [inputs, out, tfi, tfo]
    return val

  def _getEllapsedTime(self) :
    return time.time() - self.start

  def _checkTime(self) :
    x = self._getEllapsedTime()
    if x > self.total_available_time :
      return False
    else:
       return True
    
    # Only for testing
  @staticmethod
  def _progressBar(current, total, barLength = 20):
    percent = float(current) * 100 / total
    arrow   = '-' * int(percent/100 * barLength - 1) + '>'
    spaces  = ' ' * (barLength - len(arrow))
    print('Progress: [%s%s] %d %%' % (arrow, spaces, percent), end='\r')
    


class BaseCircuitTraverser :

  def __init__(self, spec, root_expander, config) :
    self.spec = spec
    self.root_expander = root_expander
    self.config = config
    self.nof_root_selection_trials = 20
    self.subcircuit_size = config.initial_subcircuit_size
    self.time_subcircuit_selection = 0

  def setUpIteration(self) :
    self.time_subcircuit_selection = 0

  def getSubcircuit(self, forbidden=[]) :
    to_replace = []
    trials = 0
    start = time.time()
    while len(to_replace) < 2 and trials < self.nof_root_selection_trials:
      trials += 1
      root_gate = self.getRoot()
      if root_gate is None:
        assert False #REMOVE: just for testing
        logging.warning(f"Could not find a root gate")
        return None
      to_replace = self.root_expander.expand(root_gate, self.subcircuit_size, forbidden)
    # replaceable, subcir_data, timeout = self._replaceSubcircuit(to_replace, self.config.gate_size)
    self.time_subcircuit_selection += (time.time() - start)
    if len(to_replace) < 2 :
      logging.info(f"Could not find a root after {self.nof_root_selection_trials} Iterations that could be expanded into a subcircuit with at least two gates.")
      return None
    return root_gate, to_replace
  
  def update(self, to_replace, synth_res) :
    pass





class CompleteCoverage(BaseCircuitTraverser) :
  def __init__(self, spec : Specification, root_expander, config) :
    super().__init__(spec, root_expander, config)
    self.spec = spec
    self.candidates = {y for x in spec.getInputs() for y in spec.getGateOutputs(x)}

  def getRoot(self) :
    if len(self.candidates) == 0 :
      self.candidates = {y for x in self.spec.getInputs() for y in self.spec.getGateOutputs(x)}
    root = chooseFromSet(self.candidates)
    self.candidates.remove(root)
    return root

  def update(self, to_replace, synth_res) :
    super().update(to_replace, synth_res)
    self.candidates.difference_update(to_replace)
    replaceable, subcir_data, timeout = synth_res
    if replaceable :
      gate_names, output_assoc, unused = subcir_data
      self.candidates.difference_update(unused)
      for out in output_assoc.values() :
        if not self.spec.isPI(out) and out is not None: # an output of a subcircuit may be represented by a PI or it may be constant
          self.candidates.update(self.spec.getGateOutputs(out))
    else :
      for out in self.spec.getSubcircuitOutputs(to_replace) :
        self.candidates.update(self.spec.getGateOutputs(out))



class RandomizedTraversal(BaseCircuitTraverser) :
  def __init__(self, spec : Specification, root_expander, config) :
    super().__init__(spec, root_expander, config)
    self.spec = spec
    self.counter = 0
    self.taboo_dict = {}

  def getRoot(self) :
    if self.config.use_taboo_list :
      to_consider = self.spec.getGateAliasesSet()
      if len(self.taboo_dict) == len(to_consider) :
        self.updateTabooList()
      to_consider.difference_update(self.taboo_dict)
      root = chooseFromSet(to_consider)
      self.taboo_dict[root] = self.counter
      return root 
    else :
      return random.choice(self.spec.getGateAliases())
    
  def updateTabooList(self) :

    while len(self.taboo_dict) > 0 and len(self.taboo_dict) >= self.config.taboo_ratio * self.spec.getNofGates() :
      last_gate, last_counter = next(iter(self.taboo_dict.items()))
      self.taboo_dict.pop(last_gate, None)

  def update(self, to_replace, synth_res) :
    super().update(to_replace, synth_res)
    replaceable, subcir_data, timeout = synth_res
    if replaceable :
      gate_names, output_assoc, unused = subcir_data
      for x in gate_names :
        self.taboo_dict[x] = self.counter
      for g in unused :
        self.taboo_dict.pop(g, None)
    else :
      for x in to_replace :
        self.taboo_dict[x] = self.counter 
    self.counter += 1 
    self.updateTabooList()

class ReconvergentTraversal(RandomizedTraversal) :
  def __init__(self, spec : Specification, root_expander, config) :
    super().__init__(spec, root_expander, config)
    self.candidates = spec.getRejoiningGates()
    if len(self.candidates) == 0 :
      self.candidates = spec.getGateAliasesSet()

  def getCandidate(self) :
    return chooseFromSet(self.candidates.difference(self.taboo_dict))

  def getRoot(self) :
    if self.config.use_taboo_list :
      if self.candidates.issubset(self.taboo_dict) :
        self.updateTabooList()
      root = self.getCandidate()
      # self.taboo_dict[root] = self.counter # how to prevent the same root to be selected in case the subcircuit is not replaceable # in general we expect that at least the first check is satisfiable
      return root 
    else :
      return chooseFromSet(self.candidates)

  def update(self, to_replace, synth_res) :
    # super().update(to_replace, synth_res)
    replaceable, subcir_data, timeout = synth_res
    old_candidates = self.candidates
    self.candidates = self.spec.getRejoiningGates()
    if len(self.candidates) == 0 :
      self.candidates = self.spec.getGateAliasesSet()
      super().update(to_replace, synth_res)
    else :
      if replaceable :
        for x in self.candidates.difference(old_candidates) :
          self.taboo_dict[x] = self.counter
        for x in old_candidates.difference(self.candidates) :
          self.taboo_dict.pop(x, None)
        
    self.counter += 1
    self.updateTabooList()




# Expands into the direction of the outputs
class BaseSubcircuitExpander :

  
  def __init__(self, spec, config, forward) :
    self.spec = spec
    self.config = config
    # Do not modify the returned list
    self.nextLevel = self.successors if forward else self.predecessors

  # do not modify the returned list
  def successors(self, gate) :
    return self.spec.getGateOutputs(gate)

  def predecessors(self, gate) :
    return [x for x in self.spec.getGateInputs(gate) if not self.spec.isPI(x)]

  def expand(self, root, size, forbidden) :
    assert root not in forbidden
    selected_gates = set()
    self.potential_successors = {root}
    while len(self.potential_successors) > 0 and len(selected_gates) < size :
      successor = self.getSuccessor(selected_gates)
      if successor is None :
        return selected_gates
      selected_gates.add(successor)
      self.update(selected_gates, successor, forbidden)
    self.reset()
    selected_gates.remove(root)
    return [root] + list(selected_gates)
  
  def reset(self) :
    self.potential_successors.clear()

class IOMinimization(BaseSubcircuitExpander) :

  def __init__(self, spec, config, forward) :
    super().__init__(spec, config, forward)
    self.subcircuit_inputs = set()
    self.nof_outputs = 0

  def getNofAdditionalInputs(self, gate, selected_gates) :
    nof_inputs = sum(1 for x in self.spec.getGateInputs(gate) if x not in selected_gates and x not in self.subcircuit_inputs)
    if gate in self.subcircuit_inputs :
      nof_inputs -= 1
    return nof_inputs
  
  def getNofAdditionalOutputs(self, gate, selected_gates) :
    selected_gates.add(gate)
    outputs = self.spec.getSubcircuitOutputs(selected_gates)
    selected_gates.remove(gate)
    return len(outputs) - self.nof_outputs
  
  def update(self, selected_gates, newGate, forbidden) :
    self.subcircuit_inputs.discard(newGate)
    self.subcircuit_inputs.update(self.spec.getGateInputs(newGate))
    self.nof_outputs = len(self.spec.getSubcircuitOutputs(selected_gates))
    self.potential_successors.discard(newGate)
    self.potential_successors.update(self.nextLevel(newGate))
    self.potential_successors.difference_update(selected_gates)
    self.potential_successors.difference_update(forbidden)

  def reset(self) :
    super().reset()
    self.subcircuit_inputs.clear()
    self.nof_outputs = 0
  
class InputMinimization(IOMinimization) :
  
  def getSuccessor(self, selected_gates) :
    assert len(self.potential_successors)
    best_nof_inputs = float("inf")
    best_nof_outputs = float("inf")
    best_level = float("inf")
    for g in self.potential_successors :
      assert g not in selected_gates, f"Tried to re-add the gate: {g} to {selected_gates}"
      current_best_nof_inputs = self.getNofAdditionalInputs(g, selected_gates)
      if current_best_nof_inputs < best_nof_inputs :
        current_best_gate = g
        best_nof_inputs = current_best_nof_inputs
        best_nof_outputs = self.getNofAdditionalOutputs(g, selected_gates)
        best_level = self.spec.getGateLevel(g)
      elif current_best_nof_inputs == best_nof_inputs :
        current_best_nof_outputs = self.getNofAdditionalOutputs(g, selected_gates)
        if current_best_nof_outputs < best_nof_outputs :
          current_best_gate = g
          best_nof_outputs = current_best_nof_outputs
          best_level = self.spec.getGateLevel(g)
        elif current_best_nof_outputs == best_nof_outputs :
          if self.spec.getGateLevel(g) < best_level :
            current_best_gate = g
            best_level = self.spec.getGateLevel(g)
    return current_best_gate

class OutputMinimization(IOMinimization) :
  
  def getSuccessor(self, selected_gates) :
    assert len(self.potential_successors)
    best_nof_inputs = float("inf")
    best_nof_outputs = float("inf")
    best_level = float("inf")
    for g in self.potential_successors :
      assert g not in selected_gates, f"Tried to re-add the gate: {g} to {selected_gates}"
      current_best_nof_outputs = self.getNofAdditionalOutputs(g, selected_gates)
      if current_best_nof_outputs < best_nof_outputs :
        current_best_gate = g
        best_nof_outputs = current_best_nof_outputs
        best_nof_inputs = self.getNofAdditionalInputs(g, selected_gates)
        best_level = self.spec.getGateLevel(g)
      elif current_best_nof_outputs == best_nof_outputs :
        current_best_nof_inputs = self.getNofAdditionalInputs(g, selected_gates)
        if current_best_nof_inputs < best_nof_inputs :
          current_best_gate = g
          best_nof_inputs = current_best_nof_inputs
          best_level = self.spec.getGateLevel(g)
        elif current_best_nof_inputs == best_nof_inputs :
          if self.spec.getGateLevel(g) < best_level :
            current_best_gate = g
            best_level = self.spec.getGateLevel(g)
    return current_best_gate

class BFSExpansion(BaseSubcircuitExpander) :

  def __init__(self, spec, config, forward) :
    super().__init__(spec, config, forward)
    self.next_level_to_consider = set()
  
  def getSuccessor(self, selected_gates) :
    return self.potential_successors.pop()

  def update(self, selected_gates, newGate, forbidden) :
    self.next_level_to_consider.update(self.nextLevel(newGate))
    if len(self.potential_successors) == 0 :
      self.potential_successors, self.next_level_to_consider = self.next_level_to_consider, self.potential_successors
      self.potential_successors.difference_update(selected_gates)
      self.potential_successors.difference_update(forbidden)

  def reset(self) :
    super().reset()
    self.next_level_to_consider.clear()

class RandomizedBFS(BaseSubcircuitExpander) :
  
  def __init__(self, spec, config, forward) :
    super().__init__(spec, config, forward)
    self.next_level_to_consider = set()
  
  def getSuccessor(self, selected_gates) :
    return self.potential_successors.pop()

  def update(self, selected_gates, newGate, forbidden) :
    self.next_level_to_consider.update(self.nextLevel(newGate))
    # self.next_level_to_consider.update(x for x in self.nextLevel(newGate) if random.uniform(0, 1) < self.config.probability_bound)
    if len(self.potential_successors) == 0 :
      # self.potential_successors, self.next_level_to_consider = self.next_level_to_consider, self.potential_successors
      self.potential_successors, self.next_level_to_consider = {x for x in self.next_level_to_consider if random.uniform(0, 1) < self.config.probability_bound}, self.potential_successors
      self.potential_successors.difference_update(selected_gates)
      self.potential_successors.difference_update(forbidden)

  def reset(self) :
    super().reset()
    self.next_level_to_consider.clear()

# CHECK:
# Probably does not make much sense
class RandomizedPath(BaseSubcircuitExpander) :

  def __init__(self, spec, config, forward) :
    super().__init__(spec, config, forward)

  def expand(self, root, size, forbidden) :
    assert root not in forbidden
    selected_gates = set()
    successors = set()
    while len(selected_gates) < size and len(successors) > 0 :
      path_length = random.randint(1, size - len(selected_gates))
      self.getPath(root, path_length, selected_gates, successors)
      successors.difference_update(selected_gates)

  def getPath(self, root, path_length, selected_gates, successors) :
    if path_length > 0 :
      successors.update(self.next(root))
      gate = random.choice(list(self.next(root)))
      selected_gates.add(gate)
      self.getPath(gate, path_length - 1, selected_gates, successors)


class SingleOutput(BaseSubcircuitExpander) :

  def __init__(self, spec, config, forward) :
    super().__init__(spec, config, True)
  
  def getSuccessor(self, selected_gates, forbidden) :
    for gate in self.potential_successors :
      gate_outputs = self.specification.getGateOutputs(gate)
      if selected_gates.issuperset(gate_outputs) :
        return gate
    return None


  def update(self, selected_gates, newGate, forbidden) :
    self.potential_successors.discard(newGate)
    self.potential_successors.update(self.nextLevel(newGate))
    self.potential_successors.difference_update(selected_gates)
    self.potential_successors.difference_update(forbidden)