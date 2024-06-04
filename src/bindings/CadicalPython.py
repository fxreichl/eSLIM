import time

from bindings.build.cadical import Cadical

from utils import TimeoutException
from utils import SolverError

class CadicalSolver:

  # class CadicalTimeoutException(Exception):
  #   pass
  
  def __init__(self, bootstrap_with=[]):
    self.solver = Cadical()
    self.append_formula(bootstrap_with)
    self.solver_time = 0
  
  def delete(self):
    del self.solver
    
  def append_formula(self, formula):
    self.solver.append_formula(formula)
    
  def add_clause(self, clause):
    self.solver.add_clause(clause)
      
  def solve(self, assumptions=[]):
    start = time.time()
    result = self.solver.solve(assumptions)
    self.solver_time = time.time() - start
    if result == 10:
      return True
    elif result == 20:
      return False
    else:
      assert False, "Invalid Cadical return status."

  def solve_limited(self, timeout, assumptions=[]) :
    if timeout == None:
      return self.solve(assumptions)
    start = time.time()
    result = self.solver.solve_limited(timeout, assumptions)
    self.solver_time = time.time() - start
    if result == 0 :
      # raise CadicalSolver.CadicalTimeoutException
      raise TimeoutException
    if result == 10:
      return True
    elif result == 20:
      return False
    else :
      raise SolverError
      # assert False, "Invalid Cadical return status."
      
  def get_failed(self, assumptions):
    return self.solver.get_failed(assumptions)
      
  
  def get_values(self, variables):
    return self.solver.get_values(variables)
      
  def get_model(self):
    return self.solver.get_model()

  def time(self) :
    return self.solver_time
