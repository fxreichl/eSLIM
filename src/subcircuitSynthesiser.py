import sys
import re
import subprocess
import time
import tempfile
import logging
import bitarray.util
import copy
import signal
from multiprocessing import current_process

from encoderCircuits import EncoderCircuits
from encoderCircuitsExact import EncoderExactSynthesis
import relationSynthesiserSAT

from relationFromSubcircuit import relationFromSubcircuit
import blifIO
import aigerIO
import utils

from utils import miniQU_path
from utils import quabs_path
from utils import qfun_path
from utils import qute_path
from utils import caqe_path
from utils import smsg_path
from utils import combineDictsCounter
from utils import combineDictsLists


from statistics import mean
from statistics import median
from statistics import stdev


class TimeManager :
  def __init__(self, config : utils.Configuration) :
    self.config = config
    # Logging
    self.total_time = 0
    self.totalised_time = 0
    self.solving_time = 0
    self.encoding_time = 0
    self.relation_time = 0
    self.relation_encoding_time = 0
    self.circuit_integration_time = 0
    self.logging_equivalent_replacements = 0

    # TEST:
    self.encoder_setup = 0
    self.cyclic_pair_detection_time = 0
    self.encode_specification = 0
    self.encode_specification_copy = 0
    self.encode_symmetry_breaking_constraints = 0
    self.encode_gate_constraints = 0


    self.timeout_per_nof_gates = {}
    self.recorded_timings_sat = {}
    self.recorded_timings_unsat = {}
    self.recorded_timeouts = {}
    self.time_spent_through_timeouts = {}

    self.recorded_relation_generation_timings = {}
    self.recorded_relation_generation_timeouts = 0

    # Timeout computation
    self.use_timeout = config.use_timeouts
    self.use_dynamic_timeouts = config.use_dynamic_timeouts
    self.required_timings = config.required_timings
    self.minimal_timeout = config.minimal_timeout
    self.base_timeout = config.base_timeout
    self.factor = config.factor
    # Adjust the mean until we recorded self.adjust_until timing 
    self.adjust_until = config.adjust_until

    # timeout for relation generation
    self.relation_generation_base_timeout = config.relation_generation_base_timeout

    self.max_chain_lenth = 0

    # extended logging
    self.sat_timings_per_nof_gates_nof_inputs = {}
    self.unsat_timings_per_nof_gates_nof_inputs = {}
    self.timeouts_per_nof_gates_nof_inputs = {}

    self.sat_timings_per_nof_gates_nof_outputs = {}
    self.unsat_timings_per_nof_gates_nof_outputs = {}
    self.timeouts_per_nof_gates_nof_outputs = {}

  # add logged data from another timemanager
  def combine(self, timer) :
    self.total_time += timer.total_time
    self.totalised_time += timer.totalised_time
    self.solving_time += timer.solving_time
    self.encoding_time += timer.encoding_time
    self.relation_time += timer.relation_time
    self.relation_encoding_time += timer.relation_encoding_time
    self.circuit_integration_time += timer.circuit_integration_time
    self.logging_equivalent_replacements += timer.logging_equivalent_replacements

    self.encoder_setup += timer.encoder_setup
    self.cyclic_pair_detection_time += timer.cyclic_pair_detection_time
    self.encode_specification += timer.encode_specification
    self.encode_specification_copy += timer.encode_specification_copy
    self.encode_symmetry_breaking_constraints += timer.encode_symmetry_breaking_constraints
    self.encode_gate_constraints += timer.encode_gate_constraints 

    # combineDictsCounter(self.timeout_per_nof_gates, timer.timeout_per_nof_gates)
    combineDictsLists(self.recorded_timings_sat, timer.recorded_timings_sat)
    combineDictsLists(self.recorded_timings_unsat, timer.recorded_timings_unsat)
    combineDictsCounter(self.recorded_timeouts, timer.recorded_timeouts)
    combineDictsCounter(self.time_spent_through_timeouts, timer.time_spent_through_timeouts)
    combineDictsLists(self.recorded_relation_generation_timings, timer.recorded_relation_generation_timings)
    self.recorded_relation_generation_timeouts += timer.recorded_relation_generation_timeouts
    self.max_chain_lenth = max(self.max_chain_lenth, timer.max_chain_lenth)
    for x in range(self.max_chain_lenth + 1) :
      if x not in self.timeout_per_nof_gates :
        self.timeout_per_nof_gates[x] = self.base_timeout

    if self.config.extended_logging :
      for nof_gates, time_dict in timer.sat_timings_per_nof_gates_nof_inputs.items() :
        if nof_gates not in self.sat_timings_per_nof_gates_nof_inputs :
          self.sat_timings_per_nof_gates_nof_inputs[nof_gates] = {}
        for nof_inputs, timings in time_dict.items() :
          if nof_inputs not in self.sat_timings_per_nof_gates_nof_inputs[nof_gates] :
            self.sat_timings_per_nof_gates_nof_inputs[nof_gates][nof_inputs] = []
          self.sat_timings_per_nof_gates_nof_inputs[nof_gates][nof_inputs] += timings

      for nof_gates, time_dict in timer.unsat_timings_per_nof_gates_nof_inputs.items() :
        if nof_gates not in self.unsat_timings_per_nof_gates_nof_inputs :
          self.unsat_timings_per_nof_gates_nof_inputs[nof_gates] = {}
        for nof_inputs, timings in time_dict.items() :
          if nof_inputs not in self.unsat_timings_per_nof_gates_nof_inputs[nof_gates] :
            self.unsat_timings_per_nof_gates_nof_inputs[nof_gates][nof_inputs] = []
          self.unsat_timings_per_nof_gates_nof_inputs[nof_gates][nof_inputs] += timings

      for nof_gates, time_dict in timer.timeouts_per_nof_gates_nof_inputs.items() :
        if nof_gates not in self.timeouts_per_nof_gates_nof_inputs :
          self.timeouts_per_nof_gates_nof_inputs[nof_gates] = {}
        for nof_inputs, nof_timeouts in time_dict.items() :
          if nof_inputs not in self.timeouts_per_nof_gates_nof_inputs[nof_gates] :
            self.timeouts_per_nof_gates_nof_inputs[nof_gates][nof_inputs] = 0
          self.timeouts_per_nof_gates_nof_inputs[nof_gates][nof_inputs] += nof_timeouts

      for nof_gates, time_dict in timer.sat_timings_per_nof_gates_nof_outputs.items() :
        if nof_gates not in self.sat_timings_per_nof_gates_nof_outputs :
          self.sat_timings_per_nof_gates_nof_outputs[nof_gates] = {}
        for nof_inputs, timings in time_dict.items() :
          if nof_inputs not in self.sat_timings_per_nof_gates_nof_outputs[nof_gates] :
            self.sat_timings_per_nof_gates_nof_outputs[nof_gates][nof_inputs] = []
          self.sat_timings_per_nof_gates_nof_outputs[nof_gates][nof_inputs] += timings

      for nof_gates, time_dict in timer.unsat_timings_per_nof_gates_nof_outputs.items() :
        if nof_gates not in self.unsat_timings_per_nof_gates_nof_outputs :
          self.unsat_timings_per_nof_gates_nof_outputs[nof_gates] = {}
        for nof_inputs, timings in time_dict.items() :
          if nof_inputs not in self.unsat_timings_per_nof_gates_nof_outputs[nof_gates] :
            self.unsat_timings_per_nof_gates_nof_outputs[nof_gates][nof_inputs] = []
          self.unsat_timings_per_nof_gates_nof_outputs[nof_gates][nof_inputs] += timings

      for nof_gates, time_dict in timer.timeouts_per_nof_gates_nof_outputs.items() :
        if nof_gates not in self.timeouts_per_nof_gates_nof_outputs :
          self.timeouts_per_nof_gates_nof_outputs[nof_gates] = {}
        for nof_inputs, nof_timeouts in time_dict.items() :
          if nof_inputs not in self.timeouts_per_nof_gates_nof_outputs[nof_gates] :
            self.timeouts_per_nof_gates_nof_outputs[nof_gates][nof_inputs] = 0
          self.timeouts_per_nof_gates_nof_outputs[nof_gates][nof_inputs] += nof_timeouts
        


  def logSatTiming(self, size, time, nof_inputs, nof_outputs) :
    self.max_chain_lenth = max(self.max_chain_lenth, size)
    self.totalised_time += time
    self.solving_time += time
    if size in self.recorded_timings_sat :
      self.recorded_timings_sat[size].append(time)
    else :
      self.recorded_timings_sat[size] = [time]

    if self.config.extended_logging :
      if size not in self.sat_timings_per_nof_gates_nof_inputs :
        self.sat_timings_per_nof_gates_nof_inputs[size] = {}
      if nof_inputs not in self.sat_timings_per_nof_gates_nof_inputs[size] :
        self.sat_timings_per_nof_gates_nof_inputs[size][nof_inputs] = []
      self.sat_timings_per_nof_gates_nof_inputs[size][nof_inputs].append(time)

      if size not in self.sat_timings_per_nof_gates_nof_outputs :
        self.sat_timings_per_nof_gates_nof_outputs[size] = {}
      if nof_outputs not in self.sat_timings_per_nof_gates_nof_outputs[size] :
        self.sat_timings_per_nof_gates_nof_outputs[size][nof_outputs] = []
      self.sat_timings_per_nof_gates_nof_outputs[size][nof_outputs].append(time)
      

  def logUnsatTiming(self, size, time, nof_inputs, nof_outputs) :
    self.max_chain_lenth = max(self.max_chain_lenth, size)
    self.totalised_time += time
    self.solving_time += time
    if size in self.recorded_timings_unsat :
      self.recorded_timings_unsat[size].append(time)
    else :
      self.recorded_timings_unsat[size] = [time]

    if self.config.extended_logging :
      if size not in self.unsat_timings_per_nof_gates_nof_inputs :
        self.unsat_timings_per_nof_gates_nof_inputs[size] = {}
      if nof_inputs not in self.unsat_timings_per_nof_gates_nof_inputs[size] :
        self.unsat_timings_per_nof_gates_nof_inputs[size][nof_inputs] = []
      self.unsat_timings_per_nof_gates_nof_inputs[size][nof_inputs].append(time)

      if size not in self.unsat_timings_per_nof_gates_nof_outputs :
        self.unsat_timings_per_nof_gates_nof_outputs[size] = {}
      if nof_outputs not in self.unsat_timings_per_nof_gates_nof_outputs[size] :
        self.unsat_timings_per_nof_gates_nof_outputs[size][nof_outputs] = []
      self.unsat_timings_per_nof_gates_nof_outputs[size][nof_outputs].append(time)
    
  def logEncodingTime(self, time) :
    self.totalised_time += time
    self.encoding_time += time

  def logRelationGenerationTime(self, size, solving_time, encoding_time) :
    self.relation_encoding_time += encoding_time
    relation_time = solving_time + encoding_time
    self.totalised_time += relation_time
    self.relation_time += relation_time
    if size in self.recorded_relation_generation_timings :
      self.recorded_relation_generation_timings[size].append(relation_time)
    else :
      self.recorded_relation_generation_timings[size] = [relation_time]

  def logRelationGenerationTimeout(self, size) :
    self.max_chain_lenth = max(self.max_chain_lenth, size)
    self.recorded_relation_generation_timeouts += 1
    relation_time = self.relation_generation_base_timeout
    self.totalised_time += relation_time
    self.relation_time += relation_time
    if size in self.recorded_relation_generation_timings :
      self.recorded_relation_generation_timings[size].append(relation_time)
    else :
      self.recorded_relation_generation_timings[size] = [relation_time]

  def logTimeout(self, size, nof_inputs, nof_outputs) :
    self.max_chain_lenth = max(self.max_chain_lenth, size)
    self.totalised_time += self.timeout_per_nof_gates[size]
    self.solving_time += self.timeout_per_nof_gates[size]
    if size in self.recorded_timeouts :
      self.recorded_timeouts[size] += 1
      self.time_spent_through_timeouts[size] += self.timeout_per_nof_gates[size]
    else :
      self.recorded_timeouts[size] = 1
      self.time_spent_through_timeouts[size] = self.timeout_per_nof_gates[size]

    if self.config.extended_logging :
      if size not in self.timeouts_per_nof_gates_nof_inputs :
        self.timeouts_per_nof_gates_nof_inputs[size] = {}
      if nof_inputs not in self.timeouts_per_nof_gates_nof_inputs[size] :
        self.timeouts_per_nof_gates_nof_inputs[size][nof_inputs] = 0
      self.timeouts_per_nof_gates_nof_inputs[size][nof_inputs] += 1

      if size not in self.timeouts_per_nof_gates_nof_outputs :
        self.timeouts_per_nof_gates_nof_outputs[size] = {}
      if nof_outputs not in self.timeouts_per_nof_gates_nof_outputs[size] :
        self.timeouts_per_nof_gates_nof_outputs[size][nof_outputs] = 0
      self.timeouts_per_nof_gates_nof_outputs[size][nof_outputs] += 1
      

  def logIntegrationTime(self, time) :
    self.totalised_time += time
    self.circuit_integration_time += time


  def isTimeoutSet(self, size) :
    return size in self.timeout_per_nof_gates

  def initTimeout(self, size) :
    for x in range(max(self.timeout_per_nof_gates, default=-1) + 1, size + 1) :
      self.timeout_per_nof_gates[x] = self.base_timeout

  def useTimeout(self) :
    return self.use_timeout

  def getTimeout(self, size) :
    if size in self.timeout_per_nof_gates :
      return self.timeout_per_nof_gates[size]
    else :
      return self.base_timeout

  def getMeanSatTime(self, size) :
    assert size in self.recorded_timings_sat and len(self.recorded_timings_sat) > 0
    return utils.mean(self.recorded_timings_sat[size])

  def _getAdjustedMeanTime(self, val) :
    return (sum(val) + self.base_timeout) / (len(val) + 1)

  def _updateTimeouts(self, nof_gates) :
    if not self.use_dynamic_timeouts :
      return
    if self.config.use_experimental_TOs :
      timeout = self._computeSTDEVbasedTO(nof_gates)
    else :
      timeout = self._computeTOsAvgBased(nof_gates)
    timeout = min(timeout, self.base_timeout)
    for x in range(nof_gates + 1) :
      self.timeout_per_nof_gates[x] = min(self.timeout_per_nof_gates[x], timeout)

  def _computeTOsAvgBased(self, nof_gates) :
    if len(self.recorded_timings_sat[nof_gates]) > self.adjust_until :
      adjusted_mean = sum(self.recorded_timings_sat[nof_gates]) / len(self.recorded_timings_sat[nof_gates])
    else :
      adjusted_mean = self._getAdjustedMeanTime(self.recorded_timings_sat[nof_gates])
    if self.factor * adjusted_mean < self.base_timeout :
       timeout = self.factor * adjusted_mean
    else :
      timeout = self.base_timeout
    return max(self.minimal_timeout, timeout)

  def _computeSTDEVbasedTO(self, nof_gates) :
    nof_timings = len(self.recorded_timings_sat[nof_gates])
    assert nof_timings > 0
    if nof_timings < 2 :
      return self.base_timeout
    mean_time = mean(self.recorded_timings_sat[nof_gates])
    stdev_time = stdev(self.recorded_timings_sat[nof_gates])
    buffer_value = self.base_timeout / nof_timings
    return mean_time + buffer_value + self.config.stdev_factor * stdev_time


  def printTotalTimings(self) :
    print(f"Time: {self.total_time}")
    # print(f"Summed Component Timings {self.totalised_time}") # DEBUG:
    print(f"Solving Time: {self.solving_time}")
    print(f"Encoding Time: {self.encoding_time}")
    print(f"Circuit Integration Time: {self.circuit_integration_time}")
    print(f"Logging Equivalent Replacements: {self.logging_equivalent_replacements}")

    # TEST:
    print(f"Cyclic Pair Detection Time: {self.cyclic_pair_detection_time}")
    print(f"Encoder Setup Time: {self.encoder_setup}")
    print(f"Encoder Specification Encoding Time: {self.encode_specification}")
    print(f"Encoder Specification Copy Encoding Time: {self.encode_specification_copy}")
    print(f"Encoder Symmetry Breaking Encoding Time: {self.encode_symmetry_breaking_constraints}")
    print(f"Encoder Gate Constraints Encoding Time: {self.encode_gate_constraints}")


    if len(self.recorded_relation_generation_timings) > 0 :
      nof_generated_relations = sum(len(self.recorded_relation_generation_timings.get(x,[])) for x in range(self.max_chain_lenth + 1))
      total_relation_generation_time = sum(sum(self.recorded_relation_generation_timings.get(x,[])) for x in range(self.max_chain_lenth + 1))

      # nof_generated_relations = sum(len(self.recorded_relation_generation_timings[x]) for x  in self.recorded_relation_generation_timings[x])
      # total_relation_generation_time = sum(sum(self.recorded_relation_generation_timings[x]) for x  in self.recorded_relation_generation_timings[x])
      print(f"Total relation encoding time: {self.relation_encoding_time}")
      print(f"Total relation generation time: {total_relation_generation_time}")
      print(f"#generated relations: {nof_generated_relations}")
      print(f"Average relation generation time: {total_relation_generation_time / nof_generated_relations}")
      print(f"#relation generation timeouts: {self.recorded_relation_generation_timeouts}")

  @staticmethod
  def _getLogLine(vals) :
    if len(vals) > 0 :
      if len(vals) > 1 :
        return f"{len(vals)}; total time: {sum(vals):.3f}; mean: {mean(vals):.3f}; max: {max(vals):.3f}; min: {min(vals):.3f}; median {median(vals):.3f}; stdev; {stdev(vals):.3f}"
      else :
        return f"{len(vals)}; total time: {sum(vals):.3f}; mean: {mean(vals):.3f}; max: {max(vals):.3f}; min: {min(vals):.3f}; median {median(vals):.3f}"
    else :
      return "0"

  def printTimingsPerCheckedSize(self) :
    # for each analysed size there must be an entry in the dict
    print(">>>>>>>>>> Timings per checked size <<<<<<<<<<")
    # for size in sorted(self.timeout_per_nof_gates) :
    for size in range(self.max_chain_lenth + 1) :
      print(f"Chain length: {size}")
      total_nof_checks = len(self.recorded_timings_sat.get(size, [])) + len(self.recorded_timings_unsat.get(size, [])) + self.recorded_timeouts.get(size, 0)
      total_time = sum(self.recorded_timings_sat.get(size, [])) + sum(self.recorded_timings_unsat.get(size, [])) + self.time_spent_through_timeouts.get(size, 0)
      if total_nof_checks > 0 :
        print(f"#checks:         {total_nof_checks}; total time: {total_time:.3f}; mean: {(total_time / total_nof_checks):.3f}")
      else :
        print(f"#checks:         0")
      print("#solved checks:  " + TimeManager._getLogLine(self.recorded_timings_sat.get(size, []) + self.recorded_timings_unsat.get(size, [])))
      print("#sat checks:     " + TimeManager._getLogLine(self.recorded_timings_sat.get(size, [])))
      print("#unsat checks:   " + TimeManager._getLogLine(self.recorded_timings_unsat.get(size, [])))
      print(f"final timeout:   {self.timeout_per_nof_gates.get(size, self.base_timeout)}")
      print(f"#timeouts:       {self.recorded_timeouts.get(size, 0)}")

      if size in self.recorded_relation_generation_timings :
        nof_generated_relations = len(self.recorded_relation_generation_timings[size])
        total_relation_generation_time = sum(self.recorded_relation_generation_timings[size])
        if nof_generated_relations > 0 :
          print(f"#generated relations: {nof_generated_relations}; total time: {total_relation_generation_time}; avg time: {total_relation_generation_time / nof_generated_relations}")
          print(f"Relation encoding time: {self.relation_encoding_time}; avg time: {self.relation_encoding_time / nof_generated_relations}")
        else :
          print(f"#generated relations: 0")

  def printExtendedStatistics(self) :
    print(">>>>>>>>>> Extended Timing Stats <<<<<<<<<<")
    print(">>>>>>>>>> Stats Per #Inputs <<<<<<<<<<")
    for size in range(self.max_chain_lenth + 1) :
      print(f"Chain length: {size}")
      nof_input_set = set()
      if size in self.sat_timings_per_nof_gates_nof_inputs :
        nof_input_set.update(self.sat_timings_per_nof_gates_nof_inputs[size])
      if size in self.unsat_timings_per_nof_gates_nof_inputs :
        nof_input_set.update(self.unsat_timings_per_nof_gates_nof_inputs[size])
      if size in self.timeouts_per_nof_gates_nof_inputs :
        nof_input_set.update(self.timeouts_per_nof_gates_nof_inputs[size])
      for nof_inputs in sorted(nof_input_set) :
        if size not in self.sat_timings_per_nof_gates_nof_inputs or nof_inputs not in self.sat_timings_per_nof_gates_nof_inputs[size] :
          nof_sat_checks = 0
        else :
          nof_sat_checks = len(self.sat_timings_per_nof_gates_nof_inputs[size][nof_inputs])
        if size not in self.unsat_timings_per_nof_gates_nof_inputs or nof_inputs not in self.unsat_timings_per_nof_gates_nof_inputs[size] :
          nof_unsat_checks = 0
        else :
          nof_unsat_checks = len(self.unsat_timings_per_nof_gates_nof_inputs[size][nof_inputs])
        if size not in self.timeouts_per_nof_gates_nof_inputs or nof_inputs not in self.timeouts_per_nof_gates_nof_inputs[size] :
          nof_timeouts = 0
        else :
          nof_timeouts = self.timeouts_per_nof_gates_nof_inputs[size][nof_inputs]
        print(f"#inputs: {nof_inputs} -- #checked: {nof_sat_checks + nof_unsat_checks + nof_timeouts}; #solved: {nof_sat_checks + nof_unsat_checks}; #timeouts: {nof_timeouts}")
        if nof_sat_checks == 0 :
          print("#sat checks: 0")
        else :
          if nof_sat_checks < 2 :
            print(f"#sat checks: {nof_sat_checks}; total time: {sum(self.sat_timings_per_nof_gates_nof_inputs[size][nof_inputs])}, avg time: {mean(self.sat_timings_per_nof_gates_nof_inputs[size][nof_inputs])}, median: {median(self.sat_timings_per_nof_gates_nof_inputs[size][nof_inputs])}")
          else :
            print(f"#sat checks: {nof_sat_checks}; total time: {sum(self.sat_timings_per_nof_gates_nof_inputs[size][nof_inputs])}, avg time: {mean(self.sat_timings_per_nof_gates_nof_inputs[size][nof_inputs])}, median: {median(self.sat_timings_per_nof_gates_nof_inputs[size][nof_inputs])}, stdev: {stdev(self.sat_timings_per_nof_gates_nof_inputs[size][nof_inputs])}")

        if nof_unsat_checks == 0 :
          print("#unsat checks: 0")
        else :
          if nof_unsat_checks < 2 :
            print(f"#unsat checks: {nof_unsat_checks}; total time: {sum(self.unsat_timings_per_nof_gates_nof_inputs[size][nof_inputs])}, avg time: {mean(self.unsat_timings_per_nof_gates_nof_inputs[size][nof_inputs])}, median: {median(self.unsat_timings_per_nof_gates_nof_inputs[size][nof_inputs])}")
          else :
            print(f"#unsat checks: {nof_unsat_checks}; total time: {sum(self.unsat_timings_per_nof_gates_nof_inputs[size][nof_inputs])}, avg time: {mean(self.unsat_timings_per_nof_gates_nof_inputs[size][nof_inputs])}, median: {median(self.unsat_timings_per_nof_gates_nof_inputs[size][nof_inputs])}, stdev: {stdev(self.unsat_timings_per_nof_gates_nof_inputs[size][nof_inputs])}")
    
    print(">>>>>>>>>> Stats Per #Outputs <<<<<<<<<<")

    for size in range(self.max_chain_lenth + 1) :
      print(f"Chain length: {size}")
      nof_input_set = set()
      if size in self.sat_timings_per_nof_gates_nof_outputs :
        nof_input_set.update(self.sat_timings_per_nof_gates_nof_outputs[size])
      if size in self.unsat_timings_per_nof_gates_nof_outputs :
        nof_input_set.update(self.unsat_timings_per_nof_gates_nof_outputs[size])
      if size in self.timeouts_per_nof_gates_nof_outputs :
        nof_input_set.update(self.timeouts_per_nof_gates_nof_outputs[size])
      for nof_outputs in sorted(nof_input_set) :
        if size not in self.sat_timings_per_nof_gates_nof_outputs or nof_outputs not in self.sat_timings_per_nof_gates_nof_outputs[size] :
          nof_sat_checks = 0
        else :
          nof_sat_checks = len(self.sat_timings_per_nof_gates_nof_outputs[size][nof_outputs])
        if size not in self.unsat_timings_per_nof_gates_nof_outputs or nof_outputs not in self.unsat_timings_per_nof_gates_nof_outputs[size] :
          nof_unsat_checks = 0
        else :
          nof_unsat_checks = len(self.unsat_timings_per_nof_gates_nof_outputs[size][nof_outputs])
        if size not in self.timeouts_per_nof_gates_nof_outputs or nof_outputs not in self.timeouts_per_nof_gates_nof_outputs[size] :
          nof_timeouts = 0
        else :
          nof_timeouts = self.timeouts_per_nof_gates_nof_outputs[size][nof_outputs]
        print(f"#outputs: {nof_outputs} -- #checked: {nof_sat_checks + nof_unsat_checks + nof_timeouts}; #solved: {nof_sat_checks + nof_unsat_checks}; #timeouts: {nof_timeouts}")
        if nof_sat_checks == 0 :
          print("#sat checks: 0")
        else :
          if nof_sat_checks < 2 :
            print(f"#sat checks: {nof_sat_checks}; total time: {sum(self.sat_timings_per_nof_gates_nof_outputs[size][nof_outputs])}, avg time: {mean(self.sat_timings_per_nof_gates_nof_outputs[size][nof_outputs])}, median: {median(self.sat_timings_per_nof_gates_nof_outputs[size][nof_outputs])}")
          else :
            print(f"#sat checks: {nof_sat_checks}; total time: {sum(self.sat_timings_per_nof_gates_nof_outputs[size][nof_outputs])}, avg time: {mean(self.sat_timings_per_nof_gates_nof_outputs[size][nof_outputs])}, median: {median(self.sat_timings_per_nof_gates_nof_outputs[size][nof_outputs])}, stdev: {stdev(self.sat_timings_per_nof_gates_nof_outputs[size][nof_outputs])}")

        if nof_unsat_checks == 0 :
          print("#unsat checks: 0")
        else :
          if nof_unsat_checks < 2 :
            print(f"#unsat checks: {nof_unsat_checks}; total time: {sum(self.unsat_timings_per_nof_gates_nof_outputs[size][nof_outputs])}, avg time: {mean(self.unsat_timings_per_nof_gates_nof_outputs[size][nof_outputs])}, median: {median(self.unsat_timings_per_nof_gates_nof_outputs[size][nof_outputs])}")
          else :
            print(f"#unsat checks: {nof_unsat_checks}; total time: {sum(self.unsat_timings_per_nof_gates_nof_outputs[size][nof_outputs])}, avg time: {mean(self.unsat_timings_per_nof_gates_nof_outputs[size][nof_outputs])}, median: {median(self.unsat_timings_per_nof_gates_nof_outputs[size][nof_outputs])}, stdev: {stdev(self.unsat_timings_per_nof_gates_nof_outputs[size][nof_outputs])}")
    

# Use the same timeouts as in another timer, but log normally
class ComparisionTimeManager(TimeManager) :
  def __init__(self, config : utils.Configuration, base_timer : TimeManager) :
    super().__init__(config)
    self.base_timer = base_timer

  def getTimeout(self, size) :
    return self.base_timer.getTimeout(size)
  
    
class Logger :

  def __init__(self, config : utils.Configuration) :
    self.config = config

    # total number of analysed subcircuits per circuit size
    self.nof_analysed_per_circuit_size = {}
    # total number of replaced subcircuits per circuit size
    self.nof_replaced_per_circuit_size = {}
    # total number of reduced subcircuits per circuit size
    self.nof_reduced_per_circuit_size = {}
    # Assigns the number of equivalent replacements to the individual circuit sizes
    self.subcir_equiv_dict = {}

    # Assigns subcircuit sizes to dicts that map input counts to tuples (a,b,c)
    # where a gives the number of analysed subcircuits, b the number of replaced subcircuits
    # and c the number of reduced subcircuits with the given number of inputs
    self.nof_subcircuit_inputs_log = {}

    # Assigns the number of checks for a given chain length
    self.total_nof_checks_per_size = {}

    self.redundant_gates = 0

  def combine(self, logger) :
    combineDictsCounter(self.nof_analysed_per_circuit_size, logger.nof_analysed_per_circuit_size)
    combineDictsCounter(self.nof_replaced_per_circuit_size, logger.nof_replaced_per_circuit_size)
    combineDictsCounter(self.nof_reduced_per_circuit_size, logger.nof_reduced_per_circuit_size)
    combineDictsCounter(self.subcir_equiv_dict, logger.subcir_equiv_dict)
    combineDictsCounter(self.total_nof_checks_per_size, logger.total_nof_checks_per_size)
    for size in logger.nof_subcircuit_inputs_log :
      if size in self.nof_subcircuit_inputs_log :
        for nof_inputs in logger.nof_subcircuit_inputs_log[size] :
          if nof_inputs in self.nof_subcircuit_inputs_log[size] :
            self.nof_subcircuit_inputs_log[size][nof_inputs][0] += logger.nof_subcircuit_inputs_log[size][nof_inputs][0]
            self.nof_subcircuit_inputs_log[size][nof_inputs][1] += logger.nof_subcircuit_inputs_log[size][nof_inputs][1]
            self.nof_subcircuit_inputs_log[size][nof_inputs][2] += logger.nof_subcircuit_inputs_log[size][nof_inputs][2]
          else :
            self.nof_subcircuit_inputs_log[size][nof_inputs] = logger.nof_subcircuit_inputs_log[size][nof_inputs].copy()
      else :
        self.nof_subcircuit_inputs_log[size] = logger.nof_subcircuit_inputs_log[size].copy()
    
    self.redundant_gates += logger.redundant_gates


  def logAnalysed(self, subcir_size : int, nof_inputs : int) :
    if subcir_size in self.nof_analysed_per_circuit_size :
      self.nof_analysed_per_circuit_size[subcir_size] += 1
      if nof_inputs in self.nof_subcircuit_inputs_log[subcir_size] :
        self.nof_subcircuit_inputs_log[subcir_size][nof_inputs][0] += 1
      else :
        self.nof_subcircuit_inputs_log[subcir_size][nof_inputs] = [1, 0, 0]
    else :
      self.nof_analysed_per_circuit_size[subcir_size] = 1
      self.nof_subcircuit_inputs_log[subcir_size] = {nof_inputs : [1, 0, 0]}

  def logReplaced(self, subcir_size : int, nof_inputs : int) :
    if subcir_size in self.nof_replaced_per_circuit_size :
      self.nof_replaced_per_circuit_size[subcir_size] += 1
    else :
      self.nof_replaced_per_circuit_size[subcir_size] = 1
    self.nof_subcircuit_inputs_log[subcir_size][nof_inputs][1] += 1

  def logEquivalentReplacement(self, subcir_size : int) :
    if subcir_size in self.subcir_equiv_dict :
      self.subcir_equiv_dict[subcir_size] += 1
    else :
      self.subcir_equiv_dict[subcir_size] = 1

  def logReduced(self, subcir_size : int, nof_inputs : int) :
    if subcir_size in self.nof_reduced_per_circuit_size :
      self.nof_reduced_per_circuit_size[subcir_size] += 1
    else :
      self.nof_reduced_per_circuit_size[subcir_size] = 1
    self.nof_subcircuit_inputs_log[subcir_size][nof_inputs][2] += 1

  def logCheckedSize(self, nof_gates) :
    if nof_gates in self.total_nof_checks_per_size :
      self.total_nof_checks_per_size[nof_gates] += 1
    else :
      self.total_nof_checks_per_size[nof_gates] = 1


  def printCountsPerSize(self) :
    print(">>>>>>>>>> Sizes per circuit size <<<<<<<<<<")
    for x in sorted(self.nof_analysed_per_circuit_size) :
      print(f"Subcircuit size: {x}")
      nof_analysed = self.nof_analysed_per_circuit_size[x]
      nof_replaced = 0
      if x in self.nof_replaced_per_circuit_size :
        nof_replaced = self.nof_replaced_per_circuit_size[x]
      nof_reduced = 0
      if x in self.nof_reduced_per_circuit_size :
        nof_reduced = self.nof_reduced_per_circuit_size[x]
  
      if x in self.subcir_equiv_dict :
        nof_equiv_replacements = 0
        if x in self.subcir_equiv_dict :
          nof_equiv_replacements = self.subcir_equiv_dict[x]
        print(f"#analysed: {nof_analysed}; #replaced: {nof_replaced}; #reduced: {nof_reduced}; #equivalent replacements: {nof_equiv_replacements}")
      else :
        print(f"#analysed: {nof_analysed}; #replaced: {nof_replaced}; #reduced: {nof_reduced}")

      for y in sorted(self.nof_subcircuit_inputs_log[x].keys()) :
        print(f"#Circuits with {y} inputs: {self.nof_subcircuit_inputs_log[x][y][0]}; #replaced: {self.nof_subcircuit_inputs_log[x][y][1]}; #reduced: {self.nof_subcircuit_inputs_log[x][y][2]}")


  def printTotalCounts(self) :
    nof_analysed = sum(self.nof_analysed_per_circuit_size.values())
    nof_replaced = sum(self.nof_replaced_per_circuit_size.values())
    nof_reduced = sum(self.nof_reduced_per_circuit_size.values())
    print(f"Total #analysed: {nof_analysed}; Total #replacements: {nof_replaced}; Total #reduction: {nof_reduced}")
    print(f"#Removed redundant gates: {self.redundant_gates}")


class SubcircuitSynthesiser :

  def __init__(self, spec, config : utils.Configuration) :
    self.specification = spec
    self.config = config
    self.timer = TimeManager(config)

    self.logger = Logger(config)

    # Iteration counter used for writing encodings
    self.subcircuit_counter = 0
    # Iteration counter used for writing log files
    self.log_counter = 0

    # Error tracing log
    self.last_cycle_constraints = []
    
    




  def reduce(self, to_replace, nof_gate_inputs, require_reduction, dependency_constraints) :
    subcircuit_inputs = self.specification.getSubcircuitInputs(to_replace)
    if len(subcircuit_inputs) < self.config.gate_size :
      return False, None, False 
    if self.config.max_nof_inputs is not None :
      if len(subcircuit_inputs) > self.config.max_nof_inputs : 
        return False, None, False 

    start = time.time()
    realisable, size, circuit, timeout = self.selectApproach(to_replace, nof_gate_inputs, require_reduction, self.timer, self.logger, self.config.synthesis_approach, dependency_constraints)
    self.timer.total_time += time.time() - start
    if realisable :
      if self.config.log_nof_equivalent_subcircuits :
        self.logEquivalentReplacement(to_replace, circuit, size)
      gates, output_association, subcircuit_inputs, gate_names = circuit
      try :
        if self.config.debug :
          spec_copy = copy.deepcopy(self.specification)
        integration_time_start = time.time()
        unused = self.specification.replaceSubcircuit(to_replace, gates, output_association)
        self.timer.logIntegrationTime(time.time() - integration_time_start)
        self.logger.redundant_gates += len(unused)
      except utils.ViolatedInvariantException as exc:
        logging.warning("Invariant violated")
        print(f"To replace: {to_replace}")
        print(f"Cycle constraints: {self.last_cycle_constraints}")
        print(f"Gates: {gates}")
        print(f"Association: {output_association}")
        if not exc.specification_error_state :
          self._logSpecification()
        elif self.config.debug :
          self._writeSpecification(spec_copy)
        raise exc
      return realisable, (gate_names, output_association, unused), False
    else :
      return realisable, None, timeout

  # supports only the QBF encoding
  def bottomUpReduction(self, to_replace, nof_gate_inputs) :
    circuit_size = 1 if not self.config.allowInputsAsOutputs and not self.config.allowConstantsAsOutputs else 0
    encoder = EncoderCircuits(self.specification, to_replace, [], self.config, self.timer)
    if len(encoder.getSubcircuitInputs()) < nof_gate_inputs :
      logging.warn(f"The given circuit must have at least {nof_gate_inputs} inputs")
      return -1
    self.use_timeout = False
    start = time.time()
    while True :
      print(f"Check size: {circuit_size}")
      current_realisable, subcir = self._checkEncoding(encoder, to_replace, circuit_size, nof_gate_inputs, self.timer)
      if current_realisable :
        break
      circuit_size += 1
    synthesis_time = time.time() - start
    logging.info(f"Used time {synthesis_time}")
    gates, output_association, subcircuit_inputs, gate_names = subcir
    self.specification.replaceSubcircuit(to_replace, gates, output_association)
    return circuit_size

  # supports only the QBF encoding
  def singleCheck(self, to_replace, size, nof_gate_inputs, encoding_file, dependency_constraints = []) :
    self.use_timeout = False
    encoder = EncoderCircuits(self.specification, to_replace, dependency_constraints, self.config)
    with open(encoding_file,"w") as out: 
      encoder.getEncoding(size, nof_gate_inputs, out)
    current_realisable, subcir = self._checkEncoding(encoder, to_replace, size, nof_gate_inputs, self.timer)
    if current_realisable :
      gates, output_association, subcircuit_inputs, gate_names = subcir
      self.specification.replaceSubcircuit(to_replace, gates, output_association)
    return current_realisable

  def selectApproach(self, to_replace, nof_gate_inputs, require_reduction, timer, logger, mode : utils.Configuration.SynthesisationMode, dependency_constraints) :
    if mode == utils.Configuration.SynthesisationMode.qbf :
      assert self.config.qbf_solver in {utils.Configuration.QBFSolver.QFun, utils.Configuration.QBFSolver.quabs, utils.Configuration.QBFSolver.miniQU, utils.Configuration.QBFSolver.SMSG}, "Invalid qbf solver selected."
      return self.synthesiseQBF(to_replace, nof_gate_inputs, require_reduction, timer, logger, dependency_constraints)
    elif mode == utils.Configuration.SynthesisationMode.exact :
      assert self.config.qbf_solver in {utils.Configuration.QBFSolver.QFun, utils.Configuration.QBFSolver.quabs, utils.Configuration.QBFSolver.miniQU, utils.Configuration.QBFSolver.SMSG}, "Invalid qbf solver selected."
      return self.synthesiseExact(to_replace, nof_gate_inputs, require_reduction, timer, logger, dependency_constraints)
    elif mode == utils.Configuration.SynthesisationMode.relation_sat :
      return self.synthesiseRelationSAT(to_replace, nof_gate_inputs, require_reduction, timer, logger, dependency_constraints)
    else :
      assert False

  def synthesiseQBF(self, to_replace, nof_gate_inputs, require_reduction, timer, logger, dependency_constraints) :
    try :
      x = time.time()
      encoder = EncoderCircuits(self.specification, to_replace, dependency_constraints, self.config, timer)
      timer.logEncodingTime(time.time() - x)
      self.last_cycle_constraints = encoder.forbidden
      if len(encoder.subcircuit_inputs) < nof_gate_inputs : 
        return False, None, None, False
      return self.synthesise(encoder, to_replace, nof_gate_inputs, require_reduction, timer, logger)
    except utils.NoOutputException :
      logging.warning("Subcrcuit with no outputs detected")
      print(f"To replace: {to_replace}")
      self._logSpecification()
      return True, ([], {}, []), False

  def synthesiseExact(self, to_replace, nof_gate_inputs, require_reduction, timer, logger, dependency_constraints) :
    try :
      x = time.time()
      encoder = self._setupEquivEncoder(to_replace)
      timer.logEncodingTime(time.time() - x)
      self.last_cycle_constraints = encoder.forbidden
      if len(encoder.inputs) < nof_gate_inputs : 
        return False, None, None, False
      return self.synthesise(encoder, to_replace, nof_gate_inputs, require_reduction, timer, logger)
    except utils.NoOutputException :
      logging.warning("Subcrcuit with no outputs detected")
      print(f"To replace: {to_replace}")
      self._logSpecification()
      return True, ([], {}, []), False



  def _xcpu_handler(self, signum, frame):
    # signame = signal.Signals(signum).name
    print(f"XCPU signal received -- terminate current check")
    raise utils.ResourceLimitException("XCPU signal received")

  def synthesiseRelationSAT(self, to_replace, nof_gate_inputs, require_reduction, timer, logger, dependency_constraints) :
    start = time.time()
    subcircuit_inputs = self.specification.getSubcircuitInputs(to_replace)
    # A subcircuit shall have at least as many inputs as an single gate should have
    if len(subcircuit_inputs) < self.config.gate_size :
      return False, None, None, False
    logger.logAnalysed(len(to_replace), len(subcircuit_inputs))
    if len(subcircuit_inputs) == 0 :
      logging.warning("Subcrcuit with no inputs detected")
      return False, None, None, False
    subcircuit_outputs = self.specification.getSubcircuitOutputs(to_replace)
    if len(subcircuit_outputs) == 0 :
      logging.warning("Subcrcuit with no outputs detected")
      return True, 0, ([], {}, None, []), False
    potential_cycles = self.specification.getPotentialCycles(subcircuit_inputs, subcircuit_outputs, to_replace) 
    self.last_cycle_constraints = potential_cycles
    setup_time = time.time() - start
    try :
      original_signal_handler = signal.getsignal(signal.SIGXCPU)
      signal.signal(signal.SIGXCPU, self._xcpu_handler)
      try :
        relation, solving_time_relation_generation, encoding_time_relation_generation = relationFromSubcircuit(self.specification, to_replace, potential_cycles, timer.relation_generation_base_timeout) 
      except utils.TimeoutException :
        timer.logRelationGenerationTimeout(len(to_replace))
        logging.info("Timeout in relation generation")
        return False, None, None, True
      except utils.ViolatedInvariantException as exc:
        logging.warning("Invariant violated")
        print(f"To replace: {to_replace}", flush=True)
        self._logSpecification()
        raise exc
      except utils.SolverError :
        timer.logRelationGenerationTimeout(len(to_replace))
        logging.warning("Solver in invalid state")
        return False, None, None, True 
      timer.logRelationGenerationTime(len(to_replace), solving_time_relation_generation, encoding_time_relation_generation + setup_time)
      sat_synthesiser = relationSynthesiserSAT.RelationSynthesiser(list(subcircuit_inputs), list(subcircuit_outputs), potential_cycles, relation, self.config)
      sat_synthesiser.setTimeingManager(timer)
      sat_synthesiser.setLogger(logger)
      try :
        status, circuit = sat_synthesiser.synthesise(len(to_replace), nof_gate_inputs, to_replace, not require_reduction)
      except utils.ViolatedInvariantException as exc:
        logging.warning("Invariant violated")
        print(f"To replace: {to_replace}", flush=True)
        print(f"Relation: {relation}", flush=True)
        print(f"Cycle constraints: {potential_cycles}", flush=True)
        self._logSpecification()
        raise exc
    except utils.ResourceLimitException :
      return False, None, None, False
    except MemoryError as e:
      print(f"Out of memory -- MemoryError")
      print(e)
      return False, None, None, False
    finally :
      signal.signal(signal.SIGXCPU, original_signal_handler)
    if status :
      if self.config.log_dir is not None and status == -1 :
        logging.warning("Not realisable")
        print(f"To replace: {to_replace}", flush=True)
        self._logSpecification()
        with open(f"{self.config.log_dir}/relation{self.log_counter}", "w") as file :
          for line in relation :
            file.write(" ".join(str(x) for x in line))
        self.log_counter += 1
      return False, None, None, False
    else :
      logger.logReplaced(len(to_replace), len(subcircuit_inputs))
      gates, output_association = circuit
      if len(gates) < len(to_replace) :
        logger.logReduced(len(to_replace), len(subcircuit_inputs))
      return True, len(gates), (gates, output_association, None, to_replace[:len(gates)]), False


  def logEquivalentReplacement(self, to_replace, new_subcircuit, size) :
    start = time.time()
    if self.isEquivalentReplacement(to_replace, new_subcircuit) :
      self.logger.logEquivalentReplacement(size)
    self.timer.logging_equivalent_replacements += time.time() - start

  def isEquivalentReplacement(self, to_replace, new_subcircuit) :
    subcircuit_inputs = list(self.specification.getSubcircuitInputs(to_replace))
    subcircuit_outputs = list(self.specification.getSubcircuitOutputs(to_replace))
    current_subcirc_io = (subcircuit_inputs, subcircuit_outputs)
    old_gates = [(g.getAlias(), g.inputs, g.table) for g in self.specification.orderedGateTraversal() if g.getAlias() in to_replace]
    old_subcir = current_subcirc_io + tuple([old_gates])
    gates, output_association, _, _ = new_subcircuit
    new_outputs = [output_association[x] for x in subcircuit_outputs]
    new_subcir = (subcircuit_inputs, new_outputs, gates)
    return utils.checkSubcircuitsForEquivalence(old_subcir, new_subcir)

  def analyseOriginalSize(self, encoder, to_replace, nof_gate_inputs, timer, clausal_encoding = False) :
    nof_gates = len(to_replace)
    try :
      # For the initial size we know that the encoding is satisfiable. Thus, we allow the maximal solving time.
      realisable, subcir_candidate = self._checkEncoding(encoder, to_replace, nof_gates, nof_gate_inputs, timer, True, clausal_encoding)
      if not realisable :
        if self.config.symmetryBreakingUsed() :
          encoder.disableSymmetryBreaking()
          realisable, subcir_candidate = self._checkEncoding(encoder, to_replace, nof_gates, nof_gate_inputs, timer, True, clausal_encoding)
        if not realisable :
          # If an AIG shall be synthesised and the given circuit is not an AIG this can happen.
          # In this case this does not mean that there is an error in the program.
          # For example if we have a subcircuit with a single XOR Gate we cannot realize this circuit with a single-gate AIG.
          logging.warning("Warning: Cannot be replaced by circuit of initial size")
          print(f"to_replace: {to_replace}")
          self._logSpecification()
          return False, None
        else :
          logging.info("Information: Symmetry breaking constraints prevented realisation")
    except subprocess.TimeoutExpired as e :
      timer.logTimeout(nof_gates, len(encoder.inputs), len(encoder.getSubcircuitOutputs()))
      return False, None
    return realisable, subcir_candidate

  def synthesise(self, encoder, to_replace, nof_gate_inputs, require_reduction, timer, logger, clausal_encoding = False) :
    if len(encoder.inputs) < nof_gate_inputs :
      print(f"The selected subcircuit has not enough inputs")
      return False, None, None, False
    logger.logAnalysed(len(to_replace), len(encoder.inputs))
    try :
      self.subcircuit_counter += 1
      realisable = False
      max_size = len(to_replace) - 1 if require_reduction else len(to_replace)
      if not timer.isTimeoutSet(max_size) :
        timer.initTimeout(max_size)
      if not require_reduction :
        logger.logCheckedSize(len(to_replace))
        realisable, subcir_candidate = self.analyseOriginalSize(encoder, to_replace, nof_gate_inputs, timer, clausal_encoding)
        if not realisable :
          return realisable, None, None, False
        smallest_representation = len(to_replace)
      bound = len(to_replace) - 1
      for nof_gates in range(bound, 0, -1) :
        try :
          logger.logCheckedSize(nof_gates)
          current_realisable, subcir = self._checkEncoding(encoder, to_replace, nof_gates, nof_gate_inputs, timer, False, clausal_encoding)
          if current_realisable :
            realisable = True
            smallest_representation = nof_gates
            subcir_candidate = subcir
          else :
            break
        except subprocess.TimeoutExpired as e :
          timer.logTimeout(nof_gates, len(encoder.inputs), len(encoder.getSubcircuitOutputs()))
          if not realisable : # used if require_reduction is True
            return False, None, None, True
          else :
            break
      
      if self.config.allowInputsAsOutputs or self.config.allowConstantsAsOutputs :
        try :
          logger.logCheckedSize(0)
          current_realisable, subcir = self._checkEncoding(encoder, to_replace, 0, nof_gate_inputs, timer, False, clausal_encoding)
          if current_realisable :
            realisable = True
            smallest_representation = 0
            subcir_candidate = subcir
        except subprocess.TimeoutExpired as e :
          logging.debug("Timeout: check for size 0")
        

      if not realisable :
        return realisable, None, None, False

      logger.logReplaced(len(to_replace), len(encoder.inputs))
      if smallest_representation < len(to_replace) :
        logger.logReduced(len(to_replace), len(encoder.inputs))

      if self.config.log_replaced_gates :
        gates, output_association, subcircuit_inputs, gate_names = subcir_candidate
        print(f"Replaced: gates: {to_replace}")
        print(f"New gates: {gate_names}")
        print(f"Output association: {output_association}")

      return realisable, smallest_representation, subcir_candidate, False
    except utils.ViolatedInvariantException as exc:
      logging.warning("Invariant violated")
      print(f"To replace: {to_replace}")
      self._logSpecification()
      raise exc

    
  def printTotalTimings(self) :
    self.timer.printTotalTimings()

  def printTimingsPerCheckedSize(self) :
    self.timer.printTimingsPerCheckedSize()

  def printCountsPerSize(self) :
    self.logger.printCountsPerSize()

  def printTotalCounts(self) :
    self.logger.printTotalCounts()


  def _getSubcircuitInformations(self, to_replace) :
    input_set = self.specification.getSubcircuitInputs(to_replace)
    output_set = self.specification.getSubcircuitOutputs(to_replace)
    return (input_set, output_set)

  def _setupEquivEncoder(self, to_replace) :
    input_set = set()
    outputs = []
    gates = []
    to_replace_set = set(to_replace)
    gate_variables = set()
    pos_set = set(self.specification.getOutputs())
    for gate in self.specification.orderedGateTraversal() :
      if gate.getAlias() in to_replace_set : 
        anded, lines = gate.getQCIRGates()        
        gates.append((gate.getAlias(), anded, lines))
        input_set.update(gate.inputs)
        gate_outputs = self.specification.getGateOutputs(gate.getAlias())
        if not to_replace_set.issuperset(gate_outputs) or gate.getAlias() in pos_set :
          outputs.append(gate.getAlias())
        gate_variables.add(gate.getAlias())
    inputs = [x for x in input_set if not x in to_replace]

    potential_cycles = self.specification.getPotentialCycles(inputs, outputs, gate_variables)
    encoder = EncoderExactSynthesis(inputs, outputs, gates, potential_cycles, self.config)
    return encoder

  def _writeEncoding(self, file, encoder, nof_gates, nof_gate_inputs) :
    start = time.time()
    encoder.getEncoding(nof_gates, nof_gate_inputs, file)
    return time.time() - start

  def _checkEncoding(self, encoder, to_replace, nof_gates, nof_gate_inputs, timer, disable_dynamic_timeout = False, clausal_encoding = False) :
    timeout = None
    if timer.useTimeout() :
      if disable_dynamic_timeout :
        timeout = timer.base_timeout
      else :
        timeout = timer.getTimeout(nof_gates)
    encoding_suffix = ".qdimacs" if clausal_encoding else ".qcir"
    if self.config.encoding_log_dir is not None :
      fname = self.config.encoding_log_dir + "/iteration_" + str(self.subcircuit_counter) + "_nofGates_" + str(nof_gates) + encoding_suffix
      with open(fname,"w") as out: 
        encoding_time = self._writeEncoding(out, encoder, nof_gates, nof_gate_inputs)
      realisable, assignment, used_time, valid = self._runSolverAndGetAssignment(fname, not encoder.hasPotentialCycles(), timeout)
    else :
      with tempfile.NamedTemporaryFile(mode = "w", suffix = encoding_suffix, delete=True) as tmp:
        encoding_time = self._writeEncoding(tmp, encoder, nof_gates, nof_gate_inputs)
        tmp.flush()
        realisable, assignment, used_time, valid = self._runSolverAndGetAssignment(tmp.name, not encoder.hasPotentialCycles(), timeout)
    timer.logEncodingTime(encoding_time)
    if not valid :
      logging.critical("QBF yielded invalid resuls -- error in encoding")
      self._logError(encoder, to_replace, len(to_replace), nof_gate_inputs)
      assert False
    if realisable :
      timer.logSatTiming(nof_gates, used_time, len(encoder.inputs), len(encoder.getSubcircuitOutputs()))
      if timer.useTimeout() :
        timer._updateTimeouts(nof_gates)
      subcircuit_data = self._extractGatesFromAssignment(to_replace, encoder, nof_gates, nof_gate_inputs, assignment)
      return realisable, subcircuit_data
    else :
      timer.logUnsatTiming(nof_gates, used_time, len(encoder.inputs), len(encoder.getSubcircuitOutputs()))
      return realisable, None

  def _extractGatesFromAssignment(self, to_replace, encoder, nof_gates, nof_gate_inputs, assignment) :
    if nof_gates <= len(to_replace) :
      gate_names = to_replace[:nof_gates]
    else :
      gate_names = to_replace + [self.specification.max_var + i + 1 for i in range(nof_gates - len(to_replace))]

    gate_definition_variables = encoder.getGateDefinitionVariables()
    selection_variables = encoder.getSelectionVariables()
    gate_output_variables = encoder.getGateOutputVariables()
    subcircuit_inputs = encoder.getSubcircuitInputs()
    subcircuit_outputs = encoder.getSubcircuitOutputs()

    gates = []
    output_association = {} # associates the outputs of the subcircuits with replaced gates
    for i in range(nof_gates) :
      inputs = []
      for j, s in enumerate(selection_variables[i]) :
        if assignment[s] == 1:
          if j < len(subcircuit_inputs) :
            inputs += [subcircuit_inputs[j]]
          else :
            inputs += [gate_names[j - len(subcircuit_inputs)]]
      
      gate_definitions = bitarray.util.zeros(2 ** nof_gate_inputs)
      # gate_definitions = [0 for k in range(2 ** nof_gate_inputs)]
      offset = 1 # We use normal gates
      for j in range(offset, 2 ** nof_gate_inputs) :
        if assignment[gate_definition_variables[i][j - offset]] == 1:
          gate_definitions[j] = 1

      gates += [(gate_names[i], inputs, gate_definitions)]

      for j, o in enumerate(gate_output_variables[i]) :
        if assignment[o] == 1:
          output_association[subcircuit_outputs[j]] = gate_names[i]

    allow_inputs_as_outputs = self.config.allowInputsAsOutputs
    allow_constants_as_outputs = self.config.allowConstantsAsOutputs

    if allow_inputs_as_outputs :
      for i in range(nof_gates, nof_gates + len(subcircuit_inputs)) :
        for j, o in enumerate(gate_output_variables[i]) :
          if assignment[o] == 1:
            output_association[subcircuit_outputs[j]] = subcircuit_inputs[i - nof_gates]

    if allow_constants_as_outputs :
      for j, o in enumerate(gate_output_variables[-1]) : 
        if assignment[o] == 1:
          output_association[subcircuit_outputs[j]] = None # If the output is a constant the output is associated to no gate

    assert len(output_association) == len(subcircuit_outputs), "Unset output detected"
    return (gates, output_association, subcircuit_inputs, gate_names)


  def _runSolverAndGetAssignment(self, input, is2QBF, timeout = None) :
    qsolver = self.config.qbf_solver
    if qsolver == utils.Configuration.QBFSolver.SMSG and not is2QBF :
      qsolver = utils.Configuration.QBFSolver.QFun
    if qsolver == utils.Configuration.QBFSolver.miniQU :
      solver_cmd = [miniQU_path, "-cert", input]
      output_pattern = r"\nV\s*(.*)\s*\n"
    elif qsolver == utils.Configuration.QBFSolver.quabs :
      solver_cmd = [quabs_path, "--partial-assignment", input]
      output_pattern = r"\nV\s*(.*)\s*r"
    elif qsolver == utils.Configuration.QBFSolver.QFun :
      solver_cmd = [qfun_path, input]
      output_pattern = r"\nv\s*(.*)\n*"
    elif qsolver == utils.Configuration.QBFSolver.SMSG :
      solver_cmd = [smsg_path, "--print-full-model", "--qcir-file", input]
      output_pattern = r"\nModel:\s*(.*)\n*"
    elif qsolver == utils.Configuration.QBFSolver.qute :
      solver_cmd = [qute_path, "--partial-certificate", input]
      output_pattern = r"SAT\n(.*)0\n"
    elif qsolver == utils.Configuration.QBFSolver.caqe :
      solver_cmd = [caqe_path, "--qdo", input]
    else :
      assert False

    start = time.time()
    result = subprocess.run(solver_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout = timeout)
    solving_time = time.time() - start
    if result.returncode == 10:
      solver_output = result.stdout.decode("utf-8")
      if self.config.qbf_solver == utils.Configuration.QBFSolver.caqe :
        assignment = self._getAssignmentCaqe(solver_output)
      else :
        assignment = self._getAssignment(solver_output, output_pattern)
      return True, assignment, solving_time, True
    elif result.returncode == 20:
      return False, [], solving_time, True
    else :
      # solver_output = result.stdout.decode("utf-8")
      # assert False, f"Error in Solver call {solver_output}"
      print("Solver message:", file=sys.stderr)
      print(result.stdout, file=sys.stderr)
      print(result.stderr, file=sys.stderr)
      return False, [], 0, False


  def _getAssignment(self, output, output_pattern) :
    st=re.search(output_pattern, output)
    assert not st is None
    assignment = {}
    assignment_str=st.groups()[0]
    for l in assignment_str.split() :
      lit = int(l)
      if lit == 0 :
        continue
      assignment[abs(lit)] = lit > 0
    return assignment

  def _getAssignmentCaqe(self, output) :
    output_pattern = r"s cnf \d+\s\d+\s\d+\n([\s\S]*)\n\nc Satisfiable"
    st=re.search(output_pattern, output)
    assert not st is None
    assignment_str=st.groups()[0]
    lines = assignment_str.split("\n")
    assignment = {}
    for line in lines :
      literal = int(line.split()[1])
      assignment[abs(literal)] = literal > 0
    return assignment

  def _logError(self, encoder, to_replace, nof_gates, nof_gate_inputs) :
    print("************ Error Log ************", file=sys.stderr)
    print(f"Root gate: {to_replace[0]}", file=sys.stderr)
    subcir_gates = " ".join(str(x) for x in to_replace)
    print(f"Subcircuit gates: {subcir_gates}", file=sys.stderr)
    print("===================================", file=sys.stderr)
    print("Specification:", file=sys.stderr)
    print("===================================", file=sys.stderr)
    blifIO.writeSpecification2Stream(sys.stderr, self.specification, "Error")
    print("", file=sys.stderr)
    print("===================================", file=sys.stderr)
    print("Encoding:", file=sys.stderr)
    print("===================================", file=sys.stderr)
    encoder.getEncoding(nof_gates, nof_gate_inputs, sys.stderr)

  def _logErrorMk2(self, to_replace, inputs, outputs, relation = None) :
    log_file = f"{self.config.log_dir}/error_{self.log_counter}"
    with open(log_file, "w") as file :
      file.write(f"To replace:\n{to_replace}\n")
      file.write(f"Inputs:\n{inputs}\n")
      file.write(f"Outputs:\n{outputs}\n")
      if relation is not None :
        file.write(f"Relation:\n{relation}\n")
      
    spec_file = f"{self.config.log_dir}/spec_{self.log_counter}.blif"
    blifIO.writeSpecification(spec_file, self.specification)



  def _logSpecification(self) :
    self._writeSpecification(self.specification)


  def _writeSpecification(self, specification) :
    if self.config.log_dir is None :
      return
    fname = f"{self.config.log_dir}/spec_"
    p = current_process()
    if len(p._identity) > 0 :
      fname += f"process{p._identity[0]}_"
    fname += str(self.log_counter)
    print(f"Specification logged as: {fname}", flush=True)
    self.log_counter += 1
    blifIO.writeSpecification(fname + ".blif", specification)
    if self.config.synthesiseAig :
      aigerIO.writeSpecification(fname + ".aag", specification)