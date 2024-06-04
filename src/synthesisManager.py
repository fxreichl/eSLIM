# import multiprocessing
import logging
import time
import random
import sys
import tempfile
import os

from synthesiser import Synthesiser
from subcircuitSynthesiser import TimeManager
from subcircuitSynthesiser import Logger
from utils import Configuration
import reduceWithAbc

from specificationManager import SpecificationManager
import multiprocessing

import blifIO
import aigerIO


class Synthesismanager :

  @staticmethod
  def getSpecification(spec, ordered_inputs = False) :
    if spec.endswith(".aig") or spec.endswith(".aag") :
      return aigerIO.getSpecification(spec)
    else :
      assert spec.endswith(".blif")
      return blifIO.getSpecification(spec, ordered_inputs)

  def __init__(self, spec_file, config : Configuration, ordered_spec = False) :
    logging.getLogger().setLevel(logging.INFO)
    self.specification = Synthesismanager.getSpecification(spec_file, ordered_spec)
    self.specification.setConfig(config)
    self.initial_nof_gates = self.specification.getNofGates()
    self.initial_depth = self.specification.getDepth()
    print(f"Initial Depth:     {self.initial_depth}")
    print(f"Initial Nof gates: {self.initial_nof_gates}")
    self.config = config
    if config.seed is None :
      self.randomSeed()
    else :
      self.setSeed(config.seed)



  def reduce(self, budget) :
    if self.config.use_windowing :
      if self.config.window_reduction == Configuration.WindowReductionMode.useAll :
        return self.reduceParallel(budget, self.config.window_reference_number, self.config.window_reference_size)
      else :
        assert False, "Invalid window reduction strategy"
    self.start = time.time()
    logger = Logger(self.config)
    timer = TimeManager(self.config)
    total_abc_time = 0
    reduced_by_abc = 0
    log_dir = self.config.log_dir
    spec_dir = self.config.specification_log_dir
    for i in range(self.config.runs) :
      if log_dir is not None and self.config.runs != 1 : 
        sub_dir = log_dir + f"/{i}"
        os.mkdir(sub_dir)
        self.config.log_dir = sub_dir
      if spec_dir is not None and self.config.runs != 1 : 
        sub_dir = spec_dir + f"/{i}"
        os.mkdir(sub_dir)
        self.config.specification_log_dir = sub_dir
      synth = self._applyReduction(budget)
      logger.combine(synth.synthesiser.logger)
      timer.combine(synth.synthesiser.timer)
      if self.config.use_abc :
        circuit_size = self.specification.getNofGates()
        spec_abc, reduced, abc_time = self._applyABC(self.specification, i)
        total_abc_time += abc_time
        print(f"ABC used time: {abc_time}")
        if reduced :
          self.specification = spec_abc
          reduced_by_abc += (circuit_size - self.specification.getNofGates())
          if self.config.specification_log_dir is not None and i < self.config.runs - 1 :
            fname = f"{self.config.specification_log_dir}/abc_run_{i}.blif"
            self.writeSpecification(fname)
        print(f"Size after application of ABC: {self.specification.getNofGates()}")
      self.config.log_dir = log_dir
          

    if self.config.use_abc :
      print(f"Total ABC time: {total_abc_time}")
      print(f"Reduced by ABC: {reduced_by_abc}")
    self.printStatistics()




  def _applyReduction(self, budget) :
    # self.run_start = time.time()
    synthesiser = Synthesiser(self.specification, self.config)
    synthesiser.reduce(budget, self.config.initial_subcircuit_size)
    return synthesiser

  def _applyABC(self, spec, iteration : int) :
    abc_start_time = time.time()
    spec_suffix = ".aig" if self.config.synthesiseAig else ".blif"
    nof_gates = self.specification.getNofGates()
    reduced_aig_fname = None
    if self.config.specification_log_dir is not None :
      reduced_aig_fname = f"{self.config.specification_log_dir}/abc_result_run_{iteration}{spec_suffix}"
    with  tempfile.NamedTemporaryFile(mode = "w", suffix = spec_suffix, delete=True) as in_file, \
          tempfile.NamedTemporaryFile(mode = "w", suffix = spec_suffix, delete=True) if reduced_aig_fname is None else open(reduced_aig_fname, 'w') as out_file:
      self.writeSpecification(in_file.name, not self.config.synthesiseAig)
      in_file.flush()
      preprocess_cmd = self.config.abc_preprocess_cmds_aig if self.config.synthesiseAig else self.config.abc_preprocess_cmds_nonaig
      process_cmd = self.config.abc_cmds_aig if self.config.synthesiseAig else self.config.abc_cmds_nonaig
      if self.config.synthesiseAig :
        gate_count = reduceWithAbc.singleABCrun(in_file.name, out_file.name, preprocess_cmd, process_cmd, self.config.synthesiseAig)
      else :
        gate_count = reduceWithAbc.applyABC(in_file.name, out_file.name, preprocess_cmd, process_cmd, self.config.synthesiseAig)
      out_file.flush()
      processed_spec = self.getSpecification(out_file.name)
      logging.info(f"ABC #gates before: {nof_gates}; after: {processed_spec.getNofGates()}")
      logging.debug(f"ABC gate count: {gate_count}; internal count: {processed_spec.getNofGates()}")
      spec_reduced = processed_spec.getNofGates() < nof_gates
      if not spec_reduced :
        logging.info("ABC increased #gates -- ABC result is not used")
    abc_time = time.time() - abc_start_time
    return processed_spec, spec_reduced, abc_time

  def setSeed(self, value) :
    self.seed = value
    random.seed(value)

  def randomSeed(self) :
    random_seed = random.randrange(sys.maxsize)
    self.setSeed(random_seed)
    logging.info(f"Used seed: {random_seed}")

  def _getEllapsedTime(self) :
    return time.time() - self.start

  def printStatistics(self) :
    current_nof_gates = self.specification.getNofGates()
    current_depth = self.specification.getDepth()
    print(f"Total time: {self._getEllapsedTime()}")
    print(f"Initial #gates: {self.initial_nof_gates}; current #gates: {current_nof_gates}")
    print(f"Initial depth: {self.initial_depth}; current depth: {current_depth}")

  def writeSpecification(self, fname, writeBlif=True) :
    if writeBlif :
      blifIO.writeSpecification(fname, self.specification)
    else :
      aigerIO.writeSpecification(fname, self.specification)


  # auxiliary method
  @staticmethod
  def _parallelReduction(synth, budget, subcircuit_size) :
    synth.reduce(budget, subcircuit_size)
    return synth
    

  # Reduce multiple windows in parallel.
  # The considered windows need to be disjoint.
  # The windows must be selected such that no cycles may arise 
  # after recombining the windows (this can be achieved by the level constraint)
  def reduceParallel(self, budget, maxparts, partsizes) :
    self.start = time.time()
    logger = Logger(self.config)
    timer = TimeManager(self.config)

    total_abc_time = 0
    reduced_by_abc = 0

    log_dir = self.config.log_dir
    spec_dir = self.config.specification_log_dir
    for i in range(self.config.runs) :
      if log_dir is not None and self.config.runs != 1 : 
        sub_dir = log_dir + f"/{i}"
        os.mkdir(sub_dir)
        self.config.log_dir = sub_dir
      if spec_dir is not None and self.config.runs != 1 : 
        sub_dir = spec_dir + f"/{i}"
        os.mkdir(sub_dir)
        self.config.specification_log_dir = sub_dir
        
      spec_manager = SpecificationManager(self.config)
      specs = spec_manager.computeWindows(self.specification, partsizes, maxparts)
      if len(specs) == 0 :
        print(f"No window could be computed.")
        return None
      for s in specs :
        s.setConfig(self.config)
      logging.info(f"#Extracted windows: {len(specs)}")
      logging.info(f"Window sizes: {[sp.getNofGates() for sp in specs]}")
      logging.info(f"Window depths: {[sp.getDepth() for sp in specs]}")
      synths = [Synthesiser(spec, self.config) for spec in specs]
      if len(synths) > 1 :
        with multiprocessing.Pool(processes = len(specs)) as pool:
          poolReturn = pool.starmap(Synthesismanager._parallelReduction, [(synth, budget, self.config.initial_subcircuit_size) for synth in synths])
      else :
        poolReturn = [Synthesismanager._parallelReduction(synths[0], budget, self.config.initial_subcircuit_size)]
      
      logger_single_run = Logger(self.config)
      timer_single_run = TimeManager(self.config)
      for x in poolReturn:
        logger_single_run.combine(x.synthesiser.logger)
        timer_single_run.combine(x.synthesiser.timer)
      logger.combine(logger_single_run)
      timer.combine(timer_single_run)

      processed_specs = [x.specification for x in poolReturn]
      self.specification = spec_manager.combine(processed_specs)

      if self.config.use_abc :
        circuit_size = self.specification.getNofGates()
        spec_abc, reduced, abc_time = self._applyABC(self.specification, i)
        total_abc_time += abc_time
        print(f"ABC used time: {abc_time}")
        if reduced :
          self.specification = spec_abc
          reduced_by_abc += (circuit_size - self.specification.getNofGates())
          if self.config.specification_log_dir is not None and i < self.config.runs - 1 :
            fname = f"{self.config.specification_log_dir}/abc_run_{i}.blif"
            self.writeSpecification(fname)
        print(f"Size after application of ABC: {self.specification.getNofGates()}")


    if self.config.use_abc :
      print(f"Total ABC time: {total_abc_time}")
      print(f"Reduced by ABC: {reduced_by_abc}")
    self.printStatistics()
