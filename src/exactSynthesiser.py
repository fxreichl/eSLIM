#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import argparse

import subcircuitSynthesiser
from utils import Configuration
import blifIO
import aigerIO
from time import process_time 


def main() :
  config = Configuration()
  if args.gs :
    nof_gate_inputs = args.gs
  else :
    nof_gate_inputs = 2
  config.gate_size = nof_gate_inputs

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

  config.synthesis_approach = Configuration.SynthesisationMode.qbf

  config.useTrivialRuleConstraint = args.N
  config.useAllStepsConstraint = args.A
  config.useNoReapplicationConstraint = args.R
  config.useOrderedStepsConstraint = args.C
  config.use_dynamic_timeouts = False
  config.synthesiseAig = False
  config.allowInputsAsOutputs = True
  config.allowConstantsAsOutputs = True
  

  if args.log_enc :
    config.encoding_log_dir = args.log_enc[0]

  config.useTrivialRuleConstraint = False
  config.useAllStepsConstraint = False
  config.useNoReapplicationConstraint = False
  config.useOrderedStepsConstraint = False

  spec = blifIO.getSpecification(args.specification)
  synth = subcircuitSynthesiser.SubcircuitSynthesiser(spec, config)
  


  t1_start = process_time()  
  gates = spec.getGateAliases()
  size = synth.bottomUpReduction(gates, nof_gate_inputs)
  t1_stop = process_time() 


  print(f"Synthesis time: {t1_stop-t1_start}")
  print(f"Minimal size: {size}")

  if args.aig :
    aigerIO.writeSpecification(args.synthesised_circuit, spec)
  else :
    blifIO.writeSpecification(args.synthesised_circuit, spec)



if __name__ == "__main__" :
  parser = argparse.ArgumentParser(description="QBF based circuit synthesis")  
  parser.add_argument('specification', metavar='SPEC',help='The specification')
  parser.add_argument('synthesised_circuit', metavar='SYN',help='The synthesised circuit')
  parser.add_argument('--gs', nargs='?', const=2, type=int, help='The number of inputs of the gates')
  parser.add_argument('--log-enc', nargs=1, help='Save the generated encodings in the given directory')
  parser.add_argument('-N', action='store_false',help='Non trivial')
  parser.add_argument('-A', action='store_false',help='All steps')
  parser.add_argument('-R', action='store_false',help='No Reapplication')
  parser.add_argument('-C', action='store_false',help='Ordered steps')
  parser.add_argument('-aig', action='store_true',help='Generate an AIG instead of a blif')
  parser.add_argument('--qbf-solver', choices=['qfun', 'miniqu', 'quabs', 'qfun2', 'smsg'], help='The solver to use')
  args = parser.parse_args()

  main()

  

