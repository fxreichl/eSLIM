import time

from specification import Specification
from utils import Configuration
import blifIO


from utils import getAllIndices

from windowGenerator import getLevelConstraintWindows

class SpecificationManager :

  def __init__(self, config : Configuration) :
    self.config = config

    # self.window_size_factor = 5
    self.window_size_factor = config.window_size_factor
    self.window_no_factor = 10
    self.trials_per_level = 5

  # the windows need to be disjoint
  def setup(self, spec : Specification, windows) :
    self.pis = spec.getInputs()
    self.pos = spec.getOutputs()
    self.negated_pos = spec.negated_pos
    contained_gates = {x for y in windows for x in y}
    aliases_complement = spec.getGateAliasesSet().difference(contained_gates)
    partitions = [Specification(list(spec.getSubcircuitInputs(x)), list(spec.getSubcircuitOutputs(x))) for x in windows]
    self.nof_partitions = len(partitions)
    # TEST: DEBUG:
    for x in partitions :
      assert len(x.getInputs()) >= self.config.gate_size
    for idx, c in enumerate(windows) :
      self.setUpSpecification(spec, partitions[idx], c)
    if len(aliases_complement) > 0 :
      self.remaining_part = Specification(list(spec.getSubcircuitInputs(aliases_complement)), list(spec.getSubcircuitOutputs(aliases_complement)))
      # We temporarily add the remaining part to simplify the processing
      partitions.append(self.remaining_part)
      self.setUpSpecification(spec, self.remaining_part, aliases_complement)
    else :
      self.remaining_part = None
    
    # TEST: DEBUG:
    # if self.config.debug and self.config.log_dir is not None :
    if self.config.log_dir is not None :
      base_name = f"{self.config.log_dir}/partition_initial_"
      for idx, pspec in enumerate(partitions) :
        fname = base_name + str(idx) + ".blif"
        blifIO.writeSpecification(fname, pspec)

    self.partition_outputs = [x.getOutputs().copy() for x in partitions]
    self.pos_association = [{} for _ in partitions] # associates outputs in the subcircuits to outputs of the whole circuit.
    pos_base = spec.getOutputs()
    pos_set_base = set(pos_base)
    for spec_idx, _ in enumerate(partitions) :
      for out_idx, out in enumerate(self.partition_outputs[spec_idx]) :
        if out in pos_set_base :
          # pos_idx = pos_base.index(out)
          pos_indices = getAllIndices(pos_base, out)
          if out_idx in self.pos_association[spec_idx] :
            self.pos_association[spec_idx][out_idx].update(pos_indices)
          else :
            q = set(pos_indices) # assigning the set directly does not work
            self.pos_association[spec_idx][out_idx] = q
    pis_base_set = set(spec.getInputs())
    inputs_used_as_outputs = pis_base_set.intersection(pos_set_base)
    self.inputs_representing_outputs = {x : [y for y in getAllIndices(pos_base, x)] for x in inputs_used_as_outputs}
    # self.inputs_representing_outputs = {x : pos_base.index(x) for x in inputs_used_as_outputs}
    if self.remaining_part is not None :
      partitions.pop()
    return partitions

  def computeWindows(self, spec : Specification, subcircuit_size, nof_subcircuits) :
    window_generation_start = time.time()
    if self.config.window_selection == Configuration.WindowSelectionMode.levelConstraint :
      windows = getLevelConstraintWindows(spec, nof_subcircuits, subcircuit_size, self.window_size_factor)
    else :
      assert False
    print(f"Time window generation: {time.time() - window_generation_start}")
    return self.setup(spec, windows)

  
  def combine(self, specs) :
    assert len(specs) == self.nof_partitions
    if self.remaining_part is not None :
      partitions = specs + [self.remaining_part]
    else :
      partitions = specs
    # if self.config.debug and self.config.log_dir is not None :
    if self.config.log_dir is not None :
      base_name = f"{self.config.log_dir}/partition_combine_"
      for idx, spec in enumerate(partitions) :
        fname = base_name + str(idx) + ".blif"
        blifIO.writeSpecification(fname, spec)
    # DEBUG:
    aliases = [x.getGateAliasesSet() for x in partitions] if self.remaining_part is None else [x.getGateAliasesSet() for x in partitions[:-1]]
    for idx, al in enumerate(aliases) :
      if idx == len(aliases) - 1 :
        break
      for j,y in enumerate(aliases[idx + 1:]) :
        if len(al.intersection(y)) != 0 :
          assert False, "The specification to combine must not overlap"
    #
    combined_pis = self.pis # the pis do not change
    combined_pos = [None] * len(self.pos)
    sub_circuits_outputs = [part.getOutputs() for part in partitions]
    for spec_idx, _ in enumerate(partitions) :
      for pos_idx, out_indices in self.pos_association[spec_idx].items() :
        for out_idx in out_indices :
          combined_pos[out_idx] = sub_circuits_outputs[spec_idx][pos_idx]
    for input, outputs in self.inputs_representing_outputs.items() :
      for out_idx in outputs :
        combined_pos[out_idx] = input
    combined_specification = Specification(combined_pis, combined_pos)
    output_renamings = {x : sub_circuits_outputs[spec_idx][idx] for spec_idx, _ in enumerate(partitions) for idx, x in enumerate(self.partition_outputs[spec_idx]) }
    for spec_idx, sub_spec in enumerate(partitions) :
      pi_set = set(sub_spec.getInputs())
      for gate in sub_spec.gateTraversal() :
        new_gate_inputs = [output_renamings[x] if x in pi_set and x in output_renamings else x for x in gate.inputs]
        combined_specification.addGateUnsorted(gate.getAlias(), new_gate_inputs, gate.table.copy()) # Do we really need to copy? The parts are not really necessary after combining
    for pos_idx, is_negated in enumerate(self.negated_pos) :
      combined_specification.negated_pos[pos_idx] = is_negated

    # Several parts may contain a constant output. 
    # But init will remove all unnecessary ones.
    # print(f"Window output renaming: {output_renamings}")
    combined_specification.init(False)
    return combined_specification

  def sortAliases(self, aliases, spec) :
    return sorted(aliases, key=spec.getGateLevel)

  def setUpSpecification(self, base : Specification, part : Specification, aliases) :
    for alias in self.sortAliases(aliases, base) :
      gate = base.getGate(alias)
      part.addGate(gate.getAlias(), gate.inputs.copy(), gate.table.copy())
    part.init()
