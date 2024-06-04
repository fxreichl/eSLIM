#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import argparse

from synthesisManager import Synthesismanager
from synthesiser import Synthesiser
from utils import Configuration

# import cProfile

def getSynthMode(val : str) :
  if val == "qbf" :
    return Configuration.SynthesisationMode.qbf
  elif val == "equivalent" :
    return Configuration.SynthesisationMode.exact
  elif val == "rel-sat" :
    return Configuration.SynthesisationMode.relation_sat
  else :
    assert False


############################################################################
# Known Limitations
# A subcircuit of size n must always be realizable by a circuits with <= n gates that obeys the respective conditions.
# This means:
#   - The tool cannot transfer a non-AIG to an AIG. A non AIG may contain XOR gates, but a XOR gate cannot be represented by a single AIG gate.
#   - The number of inputs of the gates in the specification needs to be less equal then the number of inputs of the gates that shall be synthesised.
# If a gate has inputs, then it must have at least one non constant input
# The given specification shall not contain unused gates (i.e. gates which are neither a PO nor an input to another gate)
# Subcircuits must have at least as many inputs as the gates:
#     -> e.g. if the gate size is 6 we cannot replace x = AND(i1,i2,i3), y = AND(x, i4,i5) by y = AND(i1,i2,i3,i4,i5)
# If the input is given as a blif then the blif must be sorted topologically.
############################################################################

if __name__ == "__main__" :

  synthesis_approaches = ['qbf', 'equivalent', 'rel-sat']
  parser = argparse.ArgumentParser(description="QBF based circuit synthesis")  
  parser.add_argument('specification', metavar='SPEC',help='The specification')
  parser.add_argument('synthesised_circuit', metavar='SYN',help='The synthesised circuit')
  parser.add_argument('limit', type=int, metavar='LIM',help='Available time')
  parser.add_argument('--gs', nargs=1, type=int, help='The number of inputs of the gates')
  parser.add_argument("--aig", action='store_true', help='Synthesise an AIG. Optional argument for generating an aiger output file.')
  parser.add_argument('--aig-out', nargs=1, help='AIG output file')
  parser.add_argument('--abc', action='store_true', help='Use ABC for inprocessing')
  parser.add_argument("--restarts", nargs=1, type=int, help="The number of restarts")
  parser.add_argument('--seed', nargs=1, type=int, help='Set the seed for random number generation')
  parser.add_argument('--syn-mode', choices=synthesis_approaches, help='The synthesis approach to use')
  # misc
  parser.add_argument('--qbf-solver', choices=['qfun', 'miniqu', 'quabs', "smsg"], help='The solver to use')
  parser.add_argument("--it", nargs=1, type=int, help='Stop after the given number of iterations')
  parser.add_argument("--sorted", action='store_true', help='The given specification can be considered as sorted')
  # windowing options
  parser.add_argument('--windows', nargs=2, help="The number and size of windows (no fixed limit -- values only give a reference). \nOnly if this option is set the remaining window options are used")
  parser.add_argument('--window-selection', nargs=1, type=int, help='Strategy for selecting windows (1=levelConst)')
  parser.add_argument('--window-reduction', nargs=1, type=int, help='Strategy for reducing windows (1=full)')
  parser.add_argument("--prob", nargs=1, type=float, help = "The probability bound used for the rbfs strategy")
  # Options for subcircuit selection
  parser.add_argument('--size', nargs=1, type=int, help='Set the initial subcircuit size')
  parser.add_argument("--fixed-size", action='store_false', help='Modify the subcircuit size')
  parser.add_argument("--limit-inputs", nargs=1, type=int, help='Only consider subcircuits which have at most as many inputs as given by this parameter.')
  parser.add_argument('--increase-limit', nargs=1, type=int, help='Increase subcircuits size if average sat checking time is less than the limit')
  parser.add_argument('--root-selection', choices=['random', 'reconvergent', 'coverage'], help='The strategy for selecting root gates', default='random')
  parser.add_argument('--noTaboo', action='store_false', help='Do not use a taboo list')
  parser.add_argument('--expansion', choices=["bfs", "rbfs", "inmin", "outmin", "so"], help='The expansion strategy to use', default='rbfs')
  parser.add_argument('--expansion-direction', type=int, choices=[0, 1], help='If 0 expand in the direction of the outputs')
  # Options for setting timeouts
  parser.add_argument('--dynTO', action='store_false', help='Disable dynamic timeouts')
  parser.add_argument("--solverTO", nargs=1, type=int, help = "Base timeout for the QBF/SAT checks")
  parser.add_argument("--relTO", nargs=1, type=int, help="Timeout for the relation generation (sec)")
  parser.add_argument("--stdevTO", nargs=1, type=int, help = "Consider standard deviation for TO computation")
  # Disable Symmetry Breaking Constraints
  parser.add_argument('-N', action='store_false',help='Disable Non trivial')
  parser.add_argument('-A', action='store_false',help='Disable All steps')
  parser.add_argument('-R', action='store_false',help='Disable No Reapplication')
  parser.add_argument('-O', action='store_false',help='Disable Ordered steps')
  # Further encoding options
  # Additional options for subcircuit synthesis
  parser.add_argument('--require-reduction', action='store_true', help='Only replace subcircuits by smaller subcircuits')
  parser.add_argument('--cO', action='store_false',help='Disable constants as outputs')
  parser.add_argument('--iO', action='store_false',help='Disable inputs as outputs')
  # Options to log additional information
  parser.add_argument('--log-enc', nargs=1, help='Save the generated encodings in the given directory')
  parser.add_argument('--log-spec', nargs=1, help='Log intermediate results')
  parser.add_argument('--log-iteration-steps', metavar='int-TIME',nargs=1, type=int, help="Time before logging of an intermediate result shall take place")
  parser.add_argument('--log-time-steps', metavar='int-ITERATIONS', nargs=1, type=int, help="Nof iterations before logging of an intermediate result shall take place")
  # Debug Options
  parser.add_argument('--debug', action='store_true', help='Enable debug mode')
  parser.add_argument('--log-dir', nargs=1, help='Directory for logging debug/test information')
  parser.add_argument('--trace', action='store_true', help='Trace replaced subcircuits')


  
  
  args = parser.parse_args()

  spec = args.specification
  limit = args.limit
  assert limit > 0, "The limit must be a positive number"
  config = Configuration()

  if args.gs :
    nof_gate_inputs = args.gs[0]
  else :
    nof_gate_inputs = 2
  config.gate_size = nof_gate_inputs

  if args.size :
    assert args.size[0] >= 2, "To reduce the size of a circuit, generally subcircuits with size of at least 2 must be considered."
    config.initial_subcircuit_size = args.size[0]
  else :
    config.initial_subcircuit_size = 6

  config.fixed_subcircuit_size  = args.fixed_size

  if args.increase_limit :
    if args.increase_limit[0] <= 0 :
      parser.error('increase-limit requires a positive value')
    config.subcircuit_size_increase_limit = args.increase_limit[0]

  if args.limit_inputs :
    if args.limit_inputs[0] <= 0 :
      parser.error('limit-inputs requires a positive value')
    config.max_nof_inputs = args.limit_inputs[0]


  if args.root_selection :
    if args.root_selection == 'random' :
      config.root_selection_strategy = Configuration.RootSelectionStrategy.random
      config.compute_joining_gates = False
    elif args.root_selection == 'reconvergent' :
      config.root_selection_strategy = Configuration.RootSelectionStrategy.reconvergenceBased
      config.compute_joining_gates = True
    elif args.root_selection == 'coverage' :
      config.root_selection_strategy = Configuration.RootSelectionStrategy.completeCoverage
      config.compute_joining_gates = False
    else :
      assert False, "Invalid root selection strategy"

  config.use_taboo_list = args.noTaboo

  if args.aig :
    config.synthesiseAig = True
  else :
    if args.aig_out :
      parser.error('--aig is required when --aig-out is set.')
    config.synthesiseAig = False

  if args.seed :
    config.seed = args.seed[0]
  else :
    config.seed = None

  if args.syn_mode :
    config.synthesis_approach = getSynthMode(args.syn_mode)
  else :
    config.synthesis_approach = Configuration.SynthesisationMode.qbf

  if args.qbf_solver :
    if args.qbf_solver == 'qfun' :
      config.qbf_solver = Configuration.QBFSolver.QFun
    elif args.qbf_solver == 'miniqu' :
      config.qbf_solver = Configuration.QBFSolver.miniQU
    elif args.qbf_solver == 'quabs' :
      config.qbf_solver = Configuration.QBFSolver.quabs
    elif args.qbf_solver == 'smsg' :
      config.qbf_solver = Configuration.QBFSolver.SMSG
    else :
      assert False
  else :
    config.qbf_solver = Configuration.QBFSolver.QFun

  if args.it :
    iteration_limit = args.it[0]
  else :
    iteration_limit = None

  ordered_specification = args.sorted
  # if args.single_output :
  #   config.search_strategy = Configuration.SearchStrategy.SingleOutputSubcircuit
  if args.expansion :
    if args.expansion == "bfs" :
      config.search_strategy = Configuration.SearchStrategy.exhaustiveBFS
    elif args.expansion == "rbfs" :
      config.search_strategy = Configuration.SearchStrategy.nonExhaustiveBFS
    elif args.expansion == "inmin" :
      config.search_strategy = Configuration.SearchStrategy.inputReduction
    elif args.expansion == "outmin" :
      config.search_strategy = Configuration.SearchStrategy.outputReduction
    elif args.expansion == "so" :
      config.search_strategy = Configuration.SearchStrategy.singleOutputSubcircuit
    else :
      assert False, "Invalid expansion strategy"

  if args.expansion_direction is not None :
    if args.expansion_direction == 0 :
      config.search_direction_forward = True
    else :
      config.search_direction_forward = False
  
  if args.prob :
    if args.prob[0]<=0.1 or args.prob[0] > 1 :
      parser.error("Invalid probability bound given.")
    config.probability_bound = args.prob[0]


  # config.only_single_output_subcircuits = args.single_output
  config.use_dynamic_timeouts = args.dynTO

  if args.solverTO :
    if args.solverTO[0] <= 0 :
      parser.error('Invalid timeout given')
    config.base_timeout = args.solverTO[0]
  else :
    config.base_timeout = 120

  if args.relTO :
    if args.relTO[0] <= 0 :
      parser.error("Invalid timeout given")
    config.relation_generation_base_timeout = args.relTO[0]

  if args.stdevTO :
    if args.stdevTO[0] <= 0 :
      parser.error('Invalid stdev factor given')
    config.use_experimental_TOs = True
    config.stdev_factor = args.stdevTO[0]

  config.useTrivialRuleConstraint = args.N
  config.useAllStepsConstraint = args.A
  config.useNoReapplicationConstraint = args.R
  config.useOrderedStepsConstraint = args.O

  # config.useDirectEncoding = args.direct

  config.require_reduction = args.require_reduction
  config.allowConstantsAsOutputs = args.cO
  config.allowInputsAsOutputs = args.iO
  

  if not args.log_enc and not args.log_spec and (args.log_iteration_steps or args.log_time_steps) :
    parser.error('Log steps given but neither specifications nor encodings shall be logged')
  # if not args.log_iteration_steps and not args.log_time_steps and (args.log_enc or args.log_spec) :
  #   parser.error('No log steps given although encodings or specifications shall be logged')

  if args.log_enc :
    config.encoding_log_dir = args.log_enc[0]
  else :
    config.encoding_log_dir = None
  if args.log_spec :
    config.specification_log_dir = args.log_spec[0]
  else :
    config.specification_log_dir = None
  if args.log_iteration_steps :
    config.log_iteration_steps = args.log_iteration_steps[0]
  else :
    config.log_iteration_steps = None
  if args.log_time_steps :
    config.log_time_steps = args.log_time_steps[0]
  else :
    log_time_steps = None

  config.debug = args.debug
  config.gate_count_trace = args.trace


  if args.log_dir :
    config.log_dir = args.log_dir[0]
  else :
    config.log_dir = None

  synthesiser = Synthesismanager(spec, config, ordered_specification)

  # # TEST:
  # synthesiser.writeSpecification("Initial_Spec.blif")

  if args.restarts :
    config.runs = args.restarts[0] + 1

  if args.abc :
    config.use_abc = True

  if args.windows :
    config.use_windowing = True
    config.window_reference_number = int(args.windows[0])
    config.window_reference_size = int(args.windows[1])

    if args.window_selection :
      val = int(args.window_selection[0])
      if val == 1 :
        config.window_selection = Configuration.WindowSelectionMode.levelConstraint
      else :
        parser.error('Invalid window selection strategy given')

    if args.window_reduction :
      val = int(args.window_reduction[0])
      if val == 1 :
        config.window_reduction = Configuration.WindowReductionMode.useAll
      else :
        parser.error('Invalid window reduction strategy given')

  synthesiser.reduce((limit, iteration_limit))

  # if args.parallel :
  #   nof_parts = int(args.parallel[0])
  #   part_size = int(args.parallel[1])
  #   # synthesiser.reduceParallel((limit, iteration_limit), nof_parts, part_size)
  #   synthesiser.reduceParallel((limit, iteration_limit), nof_parts, part_size)
  # elif args.sparallel :
  #   nof_parts = int(args.sparallel[0])
  #   part_size = int(args.sparallel[1])
  #   # synthesiser.reduceParallel((limit, iteration_limit), nof_parts, part_size)
  #   synthesiser.reduceParallelSimplified((limit, iteration_limit), nof_parts, part_size)
  # elif args.s2parallel :
  #   config._single_improvement = True
  #   nof_parts = int(args.s2parallel[0])
  #   part_size = int(args.s2parallel[1])
  #   synthesiser.reduceParallelSimplifiedMk2((limit, iteration_limit), nof_parts, part_size)
  # elif args.extract :
  #   part_size = int(args.extract[0])
  #   synthesiser.reducePart((limit, iteration_limit), part_size)
  # else :

  #   # pr = cProfile.Profile()
  #   # pr.enable()
  #   synthesiser.reduce((limit, iteration_limit))
  #   # pr.disable()
  #   # pr.print_stats()

  synthesiser.writeSpecification(args.synthesised_circuit)
  if args.aig and args.aig_out :
    aig_fname = args.aig_out[0]
    if not aig_fname.endswith(".aig") and not aig_fname.endswith(".aag") :
      aig_fname += ".aig"
    synthesiser.writeSpecification(aig_fname, False)

