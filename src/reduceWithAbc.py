
import tempfile
import subprocess
import shutil
import re

from utils import abc_cmd
from utils import abc_rc

def getLoadRCCommand() :
  return f"source {abc_rc}"


def getReadCommand(aig) :
  if aig:
    return "read_aiger "
  else :
    return "read_blif "

def getWriteCommand(aig) :
  if aig:
    return "write_aiger "
  else :
    return "write_blif "

def getNofGates(val, aig = True) :
  if aig :
    x = re.search(r"and\s*=\s*(\d*)", val)
  else :
    x = re.search(r"nd\s*=\s*(\d*)", val)
  if x is None :
    return None
  else :
    return int(x.groups()[0])

def applyABC(fname_in, fname_out, abc_preprocess_cmd, abc_command, aig) :
  spec_suffix = ".aig" if aig else ".blif"
  with tempfile.NamedTemporaryFile(suffix = spec_suffix, delete=True) as tmp1, tempfile.NamedTemporaryFile(suffix = spec_suffix, delete=True) as tmp2:
    write_to = tmp1
    best_tmp = tmp2
    read_command = getReadCommand(aig)
    write_command = getWriteCommand(aig)
    initial_command = f"{getLoadRCCommand()}; {read_command + fname_in}; {abc_preprocess_cmd}; {abc_command}; {write_command} {best_tmp.name}; print_stats"
    result = subprocess.run([abc_cmd, "-c", initial_command], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    abc_applications = 1
    nof_gates = getNofGates(result.stdout.decode("utf-8"), aig)
    if nof_gates is None :
      return None
    old_nof_gates = nof_gates
    improved = True
    while improved :
      current_cmd = f"{getLoadRCCommand()}; {read_command} {best_tmp.name}; {abc_command}; {write_command} {write_to.name}; print_stats"
      result = subprocess.run([abc_cmd, "-c", current_cmd], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
      abc_applications += 1
      nof_gates = getNofGates(result.stdout.decode("utf-8"), aig)
      if nof_gates is None :
        return nof_gates
      if nof_gates < old_nof_gates :
        improved = True
        x = write_to
        write_to = best_tmp
        best_tmp = x
        old_nof_gates = nof_gates
      else :
        improved = False
    if best_tmp is not None :
      shutil.copyfile(best_tmp.name, fname_out)
  print(f"ABC was called: {abc_applications} times")
  return old_nof_gates

def singleABCrun(fname_in, fname_out, abc_preprocess_cmd, abc_command, aig) :
  spec_suffix = ".aig" if aig else ".blif"
  read_command = getReadCommand(aig)
  write_command = getWriteCommand(aig)
  cmd = f"{getLoadRCCommand()}; {read_command + fname_in}; {abc_preprocess_cmd}; {abc_command}; {write_command} {fname_out}; print_stats"
  result = subprocess.run([abc_cmd, "-c", cmd], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
  nof_gates = getNofGates(result.stdout.decode("utf-8"), aig)
  return nof_gates



# def validate(spec_fname, cir_fname) :
#   cmd = f"cec -n {spec_fname} {cir_fname}"
#   result = subprocess.run([abc_path, "-c", cmd], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
