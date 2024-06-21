#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import argparse

from synthesisManager import Synthesismanager
from utils import Configuration


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
  parser = argparse.ArgumentParser(description="QBF/SAT based circuit synthesis")  
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
  parser.add_argument('--qbf-solver', choices=['qfun', 'miniqu', 'quabs', "smsg"], help='The solver to use')
  parser.add_argument('--windows', nargs=2, metavar=('#WINDOWS','SIZEWINDOWS'), help="The number and size of windows (no fixed limit -- values only give a reference). \nOnly if this option is set the remaining window options are used")
  parser.add_argument("--prob", nargs=1, type=float, help = "The probability bound used for the rbfs strategy")
  # Options for subcircuit selection
  parser.add_argument('--size', nargs=1, type=int, help='Set the initial subcircuit size')
  parser.add_argument("--fixed-size", action='store_false', help='Modify the subcircuit size')
  parser.add_argument("--limit-inputs", nargs=1, type=int, help='Only consider subcircuits which have at most as many inputs as given by this parameter.')
  # Options for setting timeouts
  parser.add_argument('--dynTO', action='store_false', help='Disable dynamic timeouts')
  parser.add_argument("--solverTO", nargs=1, type=int, help = "Base timeout for the QBF/SAT checks")
  parser.add_argument("--relTO", nargs=1, type=int, help="Timeout for the relation generation (sec)")
  # Disable Symmetry Breaking Constraints
  parser.add_argument('-N', action='store_false',help='Disable Non trivial')
  parser.add_argument('-A', action='store_false',help='Disable All steps')
  parser.add_argument('-R', action='store_false',help='Disable No Reapplication')
  parser.add_argument('-O', action='store_false',help='Disable Ordered steps')
  # Additional options for subcircuit synthesis
  parser.add_argument('--require-reduction', action='store_true', help='Only replace subcircuits by smaller subcircuits')
  parser.add_argument('--cO', action='store_false',help='Disable constants as outputs')
  parser.add_argument('--iO', action='store_false',help='Disable inputs as outputs')

  
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

  if args.limit_inputs :
    if args.limit_inputs[0] <= 0 :
      parser.error('limit-inputs requires a positive value')
    config.max_nof_inputs = args.limit_inputs[0]

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

  iteration_limit = None

  
  if args.prob :
    if args.prob[0]<=0.1 or args.prob[0] > 1 :
      parser.error("Invalid probability bound given.")
    config.probability_bound = args.prob[0]


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


  config.useTrivialRuleConstraint = args.N
  config.useAllStepsConstraint = args.A
  config.useNoReapplicationConstraint = args.R
  config.useOrderedStepsConstraint = args.O


  config.require_reduction = args.require_reduction
  config.allowConstantsAsOutputs = args.cO
  config.allowInputsAsOutputs = args.iO
  

  ordered_specification = False
  synthesiser = Synthesismanager(spec, config, ordered_specification)

  if args.restarts :
    config.runs = args.restarts[0] + 1

  if args.abc :
    config.use_abc = True

  if args.windows :
    config.use_windowing = True
    config.window_reference_number = int(args.windows[0])
    config.window_reference_size = int(args.windows[1])


  iteration_limit = None
  synthesiser.reduce((limit, iteration_limit))


  synthesiser.writeSpecification(args.synthesised_circuit)
  if args.aig and args.aig_out :
    aig_fname = args.aig_out[0]
    if not aig_fname.endswith(".aig") and not aig_fname.endswith(".aag") :
      aig_fname += ".aig"
    synthesiser.writeSpecification(aig_fname, False)

