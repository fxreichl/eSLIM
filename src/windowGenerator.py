import random
from collections import deque
import heapq

from collections import deque # for randomWindow

from specification import Specification


def getRandomWindow(spec : Specification, size : int, nof_trials : int) :
  window = []
  pis_set = set(spec.getInputs())
  for i in range(nof_trials) :
    candidate = []
    root = random.choice(list(spec.getGateAliases()))
    queue = deque([root])
    while len(candidate) < size and len(queue) > 0 :
      alias = queue.popleft()
      candidate.append(alias)
      queue.extend(x for x in spec.getGateInputs(alias) if x not in pis_set)
      # queue.extend(spec.getGateOutputs(alias))
    if len(candidate) >= size :
      return [candidate]
    if len(candidate) > len(window) :
      window = candidate
  return [window]

def getRandomisedWindowMk2(spec : Specification, size : int, nof_trials : int) :
  window = []
  pis_set = set(spec.getInputs())
  for _ in range(nof_trials) :
    candidate = []
    root = random.choice(list(spec.getGateAliases()))
    potential_successors = [root]
    touched_gates = {root}
    while len(candidate) < size and len(potential_successors) > 0 :
      alias = random.choice(potential_successors)
      candidate.append(alias)
      filtered_inputs = [x for x in spec.getGateInputs(alias) if x not in touched_gates and x not in pis_set]
      filtered_outputs = [x for x  in spec.getGateOutputs(alias) if x not in touched_gates]
      touched_gates.update(filtered_inputs)
      touched_gates.update(filtered_outputs)
      potential_successors += filtered_inputs
      potential_successors += filtered_outputs
    if len(candidate) > size :
      return [candidate]
    if len(candidate) > len(window) :
      window = candidate
  return [window]
    


# cf. Scalable Logic Synthesis using a Simple Circuit Structure, Mishchenko, IWLS06
def getRandomWindowIWLS07(spec : Specification, size : int, nof_trials : int) :
  window = []
  for _ in range(nof_trials) :
    root = random.choice(list(spec.getGateAliases()))
    candidate = getWindowIWLS07(root, spec, 15)
    if len(candidate) >= size :
      return [list(candidate)]
    if len(candidate) > len(window) :
      window = candidate
  return [list(window)]

def getWindowIWLS07(root, spec : Specification, max_distance : int) :
  in1 = getTFI(spec, {root}, max_distance)
  out1 = getTFO(spec, {root}, max_distance)
  in2 = getTFI(spec, out1, 2 * max_distance)
  out2 = getTFO(spec, in1, 2 * max_distance)
  return in2.intersection(out2)

def inputFilter(spec : Specification, gate, filter) :
  for x in spec.getGateInputs(gate) :
    if x not in filter :
      yield x

def getTFI(spec : Specification, nodes, max_distance) :
  if max_distance == 0 :
    return nodes
  pi_set = set(spec.getInputs())
  to_consider = deque((x,1) for n in nodes for x in inputFilter(spec, n, pi_set))
  while len(to_consider) > 0 :
    gate, distance = to_consider.popleft()
    if gate in nodes :
      continue
    nodes.add(gate)
    if distance < max_distance :
      to_consider.extend((x, distance + 1) for x in inputFilter(spec, gate, pi_set))
  return nodes


def getTFO(spec : Specification, nodes, max_distance) :
  if max_distance == 0 :
    return nodes
  to_consider = deque((x,1) for n in nodes for x in spec.getGateOutputs(n))
  while len(to_consider) > 0 :
    gate, distance = to_consider.popleft()
    if gate in nodes :
      continue
    nodes.add(gate)
    if distance < max_distance :
      to_consider.extend((x, distance + 1) for x in spec.getGateOutputs(gate))
  return nodes
  

  # TEST: DEBUG:
def _invariantValidation(spec : Specification, gates) :
  if len(gates) == 0 :
    return
  inputs = spec.getSubcircuitInputs(gates)
  # outputs = spec.getSubcircuitOutputs(gates)
  outputs = spec.getGatesWithSuccessor(gates)
  if len(outputs) == 0 : # POs are not an issue for the level constraint
    return
  max_input_level = max(spec.getGateLevel(x) for x in inputs)
  min_output_level = min(spec.getGateLevel(x) for x in outputs)
  assert max_input_level <= min_output_level, "Window level constraint not satisfied"


def getMaxInputLevel(spec : Specification, gates) :
  return max(spec.getGateLevel(x) for x in spec.getSubcircuitInputs(gates))

def getMinOutputLevel(spec : Specification, gates) :
  outputs = spec.getGatesWithSuccessor(gates)
  # If there are no gates with successors the level constraint will be satisfied no matter which inputs are used
  # If we use spec.getDepth() + 1 as the minimal output level the constraint will always be satisfied.
  if len(outputs) == 0 :
    return spec.getDepth() + 1
  return min(spec.getGateLevel(x) for x in outputs)

# compute windows with the property that each inputs has a smaller level as each output
# the size s of the generated window satisfies window_size / size_bound <= s <= window_size * size_bound
def getLevelConstraintWindows(spec : Specification, max_nof_windows : int, window_size : int, size_bound : float) :
  windows = []
  # If we would expand a gate that is a successor of another window we would need to add gates from this window.
  # This means that the generated windows would overlap
  potential_window_inputs = spec.getGatesAtLevel(1)
  gates_in_windows = set()
  min_size = window_size / size_bound
  while len(windows) < max_nof_windows and len(potential_window_inputs) > 0 :
    alias = random.choice(list(potential_window_inputs))
    w = computeLevelConstraintWindow2(spec, alias, window_size, size_bound, gates_in_windows)
    potential_window_inputs.difference_update(w) # really a good idea in case of len(w) < min_size?
    # DEBUG:
    for x in windows :
      assert len(w.intersection(x)) == 0
    _invariantValidation(spec, w)

    if len(w) < min_size :
      continue
    windows.append(w)
    gates_in_windows.update(w)
    w_out = spec.getDirectSuccessors(w)
    potential_window_inputs.update(w_out)
    # An input that was already reduced can be added again
    potential_window_inputs.difference_update(gates_in_windows)
  return windows




# Only mark outputs for to process
def computeLevelConstraintWindow2(spec : Specification, alias : int, window_size : int, size_bound : float, forbidden) :
  gates_to_consider = [(spec.getGateLevel(x), x) for x in spec.getGateOutputs(alias)]
  heapq.heapify(gates_to_consider)
  window = {alias}
  max_size = window_size * size_bound
  seen = {alias}
  while len(gates_to_consider) > 0 and len(window) < window_size :
    lv, gate = heapq.heappop(gates_to_consider)
    minimal_output_level = getMinOutputLevel(spec, window)
    expansion = levelConstraintGateExpansion2(gate, spec, window, forbidden, minimal_output_level)
    if expansion is None :
      continue
    if len(expansion) + len(window) > max_size :
      continue
    window.update(expansion)
    seen.update(expansion)
    expansion_outputs = getExpansionOutputs(spec, window, expansion)
    expansion_outputs.discard(gate)
    for x in expansion_outputs :
      for y in spec.getGateOutputs(x) :
        if y not in seen :
          heapq.heappush(gates_to_consider, (spec.getGateLevel(y), y))
        seen.add(y)
    new_gates = spec.getGateOutputs(gate)
    for x in new_gates :
      if x not in seen :
        heapq.heappush(gates_to_consider, (spec.getGateLevel(x), x))
    seen.update(new_gates)
  return window

def levelConstraintGateExpansion2(alias : int, spec : Specification, window, forbidden, min_out_level : int) :
  to_check = {alias}
  expansion = set()
  while len(to_check) > 0 :
    gate = to_check.pop()
    if gate in window or gate in expansion :
      continue
    if spec.getGateLevel(gate) < min_out_level :
      continue
    if gate in forbidden :
      return None
    if spec.getGateLevel(gate) >= min_out_level :
      expansion.add(gate)
      inputs = spec.getGateInputs(gate)
      to_check.update(inputs)
  return expansion

def getExpansionOutputs(spec : Specification, window, expansion) :
  alias_set = window.union(expansion)
  return set(x for x in expansion if not spec.getGateOutputs(x).issubset(alias_set))
