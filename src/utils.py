
import tempfile
import subprocess
import os
import random
from enum import Enum

ScriptDir = os.path.dirname(os.path.realpath(__file__))
####################################################################
# Program Paths
miniQU_path = f"{ScriptDir}/../QBF-Solver/miniQU"
quabs_path  = f"{ScriptDir}/../QBF-Solver/quabs"
qfun_path   = f"{ScriptDir}/../QBF-Solver/qfun"
qute_path   = f"{ScriptDir}/../QBF-Solver/qute"
caqe_path   = f"{ScriptDir}/../QBF-Solver/caqe"
smsg_path   = f"{ScriptDir}/../QBF-Solver/smsg"
abc_path    = ""
####################################################################
abc_cmd     = f"{abc_path}/build/abc"
abc_rc      = f"{abc_path}/abc.rc"

class TimeoutException(Exception):
  pass

class ResourceLimitException(Exception) :
  pass

# Memory out
class SolverError(Exception) :
  pass

class NoOutputException(Exception) :
  pass

class NotEnoughPIsException(Exception) :
  pass

# Debug:
class ViolatedInvariantException(Exception) :
  def __init__(self, message, specification_error_state=False):            
    super().__init__(message)
    self.specification_error_state = specification_error_state


class Configuration :

  class RootSelectionStrategy :
    random = 1
    reconvergenceBased = 2
    completeCoverage = 3

  class SearchStrategy(Enum):
    exhaustiveBFS = 1
    nonExhaustiveBFS = 2
    inputReduction = 3
    outputReduction = 4
    singleOutputSubcircuit = 5


  class QBFSolver(Enum):
    miniQU = 1
    quabs = 2
    QFun = 3
    qute = 4
    caqe = 5    # version >= 4
    SMSG = 6
    
  class SynthesisationMode(Enum) :
    qbf = 1
    qbf_clausal = 2
    exact = 3
    relation_sat = 4

  class WindowSelectionMode(Enum) :
    levelConstraint = 1       # Ensure that all inputs have a smaller level than all outputs

  class WindowReductionMode(Enum) :
    useAll = 1                # Reduce windows in parallel and use all reductions


  def __init__(self) :
    # General Options
    self.runs = 1 # if a value > is chosen start synthesis again when the budget is used up
    self.seed = None # if None randomise the seed
    self.synthesiseAig = True
    # ABC options
    self.use_abc = False

    self.abc_preprocess_cmds_aig = ""
    self.abc_cmds_aig = "&get -n; &deepsyn -T 180; &put"

    self.abc_preprocess_cmds_nonaig = ""
    self.abc_cmds_nonaig = "&get -m; &mfs -a; &put"
    # Circuit Traversal Options
    self.root_selection_strategy = Configuration.RootSelectionStrategy.random
    # self.traversal_strategy = 1 
    self.probability_bound = 0.8
    self.search_direction_forward = True
    self.use_taboo_list = True
    self._single_improvement = False # Stop after the first reduction
    # Subcircuit selection Options
    self.subcircuit_size_validation_number = 20 #1 #number of trials to validate a subcircuit size
    self.initial_subcircuit_size = 6
    self.fixed_subcircuit_size = False #if true don't increase the subcircuit size
    self.max_nof_inputs = None #if not none: gives the maximal number of inputs a subcircuit may have,
    # TODO: Find good values
    self.taboo_ratio = 0.6 # 0 < self.taboo_ratio < 1
    self.check_subcircuit_size_interval = 50  # 100
    self.subcircuit_size_increase_limit = 30 # self.subcircuit_size_increase_limit > 0
    self.subcircuit_size_increase_nof_samples = 50
    # Compute the nodes where reconvergent paths join again
    self.compute_joining_gates = False
    # self.only_single_output_subcircuits = False
    self.search_strategy = Configuration.SearchStrategy.inputReduction
    # Synthesis Approach
    self.synthesis_approach = Configuration.SynthesisationMode.qbf
    # Window Options
    self.use_windowing = False
    self.window_selection = Configuration.WindowSelectionMode.levelConstraint
    # self.window_selection = Configuration.WindowSelectionMode.randomisedLevelConstraint
    self.window_reduction = Configuration.WindowReductionMode.useAll
    self.window_reference_size = 1000
    self.window_reference_number = 8
    self.window_size_factor = 2 # 5
    # Subcircuit Synthesis Options
    self.require_reduction = False
    # If a circuit qbf encoding (qbf, exact) is used neither qute nor caqe shall be used
    self.qbf_solver = Configuration.QBFSolver.QFun 
    # Encoding Options
    self.gate_size = 2 # nof of inputs the synthesised gates shall have
    self.useTrivialRuleConstraint = True
    self.useAllStepsConstraint = True
    self.useNoReapplicationConstraint = True
    self.useOrderedStepsConstraint = True
    self.allowInputsAsOutputs = True
    self.allowConstantsAsOutputs = True
    # Timeout Options
    self.use_timeouts = True  # Use timeouts for the individual checks
    self.use_dynamic_timeouts = True # Update the timeouts for the individual checks according to timings of the previous checks
    # self.total_available_time = 18000 # (sec)
    self.base_timeout = 120 # (sec) Initial timeout for the individual synthesis checks
    self.relation_generation_base_timeout = 240 # (sec)
    self.minimal_timeout = 1
    self.required_timings = 10
    self.factor = 1.4 
    self.adjust_until = 50
    # Logging Options
    self.gate_count_trace = False # Print the number of gates in each iteration
    self.log_nof_equivalent_subcircuits = False
    self.log_replaced_gates = False
    self.encoding_log_dir = None
    self.specification_log_dir = None
    self.log_time_steps = None
    self.log_iteration_steps = None
    # Debug Options
    self.log_dir = None
    self.debug = False
    self.extended_logging = True

    self.use_experimental_TOs = False
    self.stdev_factor = 2
 

  def getApproachName(self) : 
    if self.synthesis_approach == Configuration.SynthesisationMode.qbf :
      return "QBF"
    elif self.synthesis_approach == Configuration.SynthesisationMode.qbf_clausal :
      return "QBF Clausal"
    elif self.synthesis_approach == Configuration.SynthesisationMode.exact :
      return "QBF Exact"
    elif self.synthesis_approach == Configuration.SynthesisationMode.relation_sat :
      return "SAT Relation"
    else :
      assert False

  def symmetryBreakingUsed(self) :
    return self.useTrivialRuleConstraint or self.useAllStepsConstraint or self.useNoReapplicationConstraint or self.useOrderedStepsConstraint


  def validateConfig(self) :
    # assert self.traversal_strategy in {1}, "Invalid traversal strategy selected"
    assert 0 < self.taboo_ratio and self.taboo_ratio < 1, "Invalid taboo_ratio"
    assert 0 < self.probability_bound and self.probability_bound < 1, "Invalid probability bound"
    assert self.subcircuit_size_increase_limit > 0, "Invalid subcircuit_size_increase_limit"
    if self.synthesis_approach in {Configuration.SynthesisationMode.qbf, Configuration.SynthesisationMode.exact} :
      assert self.qbf_solver in {Configuration.QBFSolver.miniQU, Configuration.QBFSolver.QFun, Configuration.QBFSolver.SMSG, Configuration.QBFSolver.quabs}, "Invalid QBF solver selected"
    if self.synthesis_approach in {Configuration.SynthesisationMode.qbf_clausal} :
      assert self.qbf_solver in {Configuration.QBFSolver.miniQU, Configuration.QBFSolver.qute, Configuration.QBFSolver.caqe}, "Invalid QBF solver selected"
    # assert self.total_available_time > 0, "Timeouts must be positive numbers"
    assert self.base_timeout > 0, "Timeouts must be positive numbers"




# Only the second subcircuit may contain constant (False) outputs.
# A constant output is represented by the entry None in the second component of subcir2
def checkSubcircuitsForEquivalence(subcir1, subcir2) :

  with tempfile.NamedTemporaryFile(mode="w") as tmp:
    
    tmp.write("#QCIR-G14\n")

    inputs1, outputs1, gates1 = subcir1
    inputs2, outputs2, gates2 = subcir2

    assert inputs1 == inputs2
    assert len(outputs1) == len(outputs2)

    input_str = ", ".join([str(x) for x in inputs1])
    tmp.write(f"exists({input_str})\n")
    output_var = "o1"
    tmp.write(f"output({output_var})\n")

    max_input = max(inputs1)
    max_gate1 = max(x for x,_,_ in gates1)
    max_gate2 = max(x for x,_,_ in gates2) if len(gates2) > 0 else 0
    max_var = max(max_input, max_gate1, max_gate2)

    gate_names = set()
    for gate in gates1 :
      gate_var, inputs, table = gate
      gate_names.add(gate_var)
      max_var = writeGateFromTable(tmp, gate_var, inputs, table, max_var)
    
    renaming = {}
    for gate in gates2:
      gate_var, inputs, table = gate
      if gate_var in gate_names :
        max_var += 1
        renaming[gate_var] = max_var
        gate_var = max_var
      inputs = [renaming[x] if x in renaming else x for x in inputs]
      max_var = writeGateFromTable(tmp, gate_var, inputs, table, max_var)

    equiv_vars = []
    for idx, out1 in enumerate(outputs1) :
      out2 = outputs2[idx]
      if out2 is None : # a constant negative output
        # if the output is constant then there outputs are equivalent if the other one is true.
        equiv_vars.append(-out1)
        continue
      if out2 in renaming :
        out2 = renaming[out2]
      max_var += 1
      equiv_var = max_var
      equiv_vars.append(equiv_var)
      max_var = writeXor(tmp, equiv_var, out1, out2, max_var)

    equiv_vars_str = ", ".join([str(x) for x in equiv_vars])
    tmp.write(f"{output_var} = or({equiv_vars_str})\n")

    tmp.flush()
    # We use a QBF solver instead of a SAT solver as the instances are usually very easy and we do not want to add an additional dependency.
    solver_cmd = [ScriptDir + "/../QBF-Solver/qfun", tmp.name]
    result = subprocess.run(solver_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    if result.returncode == 10: # There is an assignment for the inputs such that the circuits differ -> circuits are not equivalent
      return False
    elif result.returncode == 20: # There is no assignment for the inputs such that the circuits differ -> circuits are equivalent
      return True
    else :
      print("Subcircuit equiv check:")
      print(result.stdout)
      print(result.stderr)
      with open(tmp.name, "r") as encoding :
        for line in encoding :
          print(line, end="")
      assert(False)


# not equivalent
def writeXor(out, gate_var, in1, in2, max_var) :
  max_var += 1
  aux1 = max_var
  max_var += 1
  aux2 = max_var

  out.write(f"{aux1} = or({in1}, {in2})\n")
  out.write(f"{aux2} = or({-in1}, {-in2})\n")
  out.write(f"{gate_var} = and({aux1}, {aux2})\n")
  return max_var


def writeGateFromTable(out, gate_var, inputs, table, max_var) :
  anded = len([x for x in table if x > 0]) <= (2 ** (len(inputs) - 1))
  val = 1 if anded else 0
  lines = [getBits(x, len(inputs)) for x, y in enumerate(table) if y == val]
  aux_gates = []
  if len(lines) == 1 :
    line = lines[0]
    args = [inputs[idx] if x > 0 else -inputs[idx] for idx, x in enumerate(line)]
    if anded :
      args_str = ", ".join([str(x) for x in args])
      out.write(f"{gate_var} = and({args_str})\n")
    else :
      args_str = ", ".join([str(-x) for x in args])
      out.write(f"{gate_var} = or({args_str})\n")
  else :
    for line in lines :
      args = [inputs[idx] if x > 0 else -inputs[idx] for idx, x in enumerate(line)]
      max_var += 1
      aux_gate = max_var
      aux_gates.append(aux_gate)
      if anded :
        args_str = ", ".join([str(x) for x in args])
        out.write(f"{aux_gate} = and({args_str})\n")
      else :
        args_str = ", ".join([str(-x) for x in args])
        out.write(f"{aux_gate} = or({args_str})\n")
    aux_gates_str = ", ".join([str(x) for x in aux_gates])
    if anded :
      out.write(f"{gate_var} = or({aux_gates_str})\n")
    else :
      out.write(f"{gate_var} = and({aux_gates_str})\n")
  return max_var

# truth table operations
def negateTable(table) :
  return ~table

def isNormalised(table) :
  return table[0] == 0

# most significant bit index 0, least significant bit index -1
# bitwise representation of an integer n with n>=0 with nof_bits bits
def getBits(n, nof_bits) :
  return [n >> i & 1 for i in range(nof_bits - 1, -1, -1)]

# most significant bit index 0, least significant bit index -1
def getBitSeq(n, nof_bits) :
  for i in range(nof_bits - 1, -1, -1) :
    yield n >> i & 1

def mean(vals) :
  assert len(vals) > 0
  return sum(vals) / len(vals)
 
def combineDictsCounter(dict1, dict2) :
  for key, val in dict2.items() :
    if key in dict1 :
      dict1[key] += val
    else :
      dict1[key] = val
  return dict1

def combineDictsLists(dict1, dict2) :
  for key, val in dict2.items() :
    if key in dict1 :
      dict1[key] += val
    else :
      dict1[key] = val.copy()
  return dict1

def getAllIndices(lst, val) :
  # return [idx for idx, x in enumerate(lst) if x == val]
  for idx, x in enumerate(lst) :
    if x == val :
      yield idx 

def chooseFromSet(x) :
  if len(x) == 0 :
    return None
  rv = random.randint(0, len(x) - 1)
  for idx, val in enumerate(x) :
    if idx == rv :
      return val
