#ifndef CADICAL_IPASIR_H_
#define CADICAL_IPASIR_H_

#include <stdlib.h> 

#include <vector>
#include <algorithm>
#include <chrono>

#include "cadical/src/cadical.hpp"

//DEBUG:
#include <iostream>
#include <fstream>


namespace circuit_synthesis {

using Clause = std::vector<int>;

class CadicalSolver {

 public:
  ~CadicalSolver();
  void appendFormula(const std::vector<Clause>& formula);
  void addClause(const Clause& clause);
  void addClause(Clause&& clause);
  void addCombinedClause(const Clause& cl1, const Clause& cl2, const Clause& cl3);
  void addCombinedClause(const Clause& cl1, const Clause& cl2, Clause&& cl3);
  void assume(const std::vector<int>& assumptions);
  void assume(std::vector<int>&& assumptions);
  int solve(double timeout, const std::vector<int>& assumptions);
  int solve(const std::vector<int>& assumptions);
  int solve();
  std::vector<int> getFailed(const std::vector<int>& assumptions);
  std::vector<int> getValues(const std::vector<int>& variables);
  std::vector<int> getModel();
  double getRunTime() const;
  bool isReady() const;

 private:
  void assumeAll(const std::vector<int>& assumptions);
  int val(int variable);
  double last_runtime;
  CaDiCaL::Solver solver;

 public: 
  class TimeoutTerminator : public CaDiCaL::Terminator {
   public:
    TimeoutTerminator(double max_runtime);
    bool terminate();

   private:
    double max_runtime; //in seconds
    std::chrono::time_point<std::chrono::steady_clock> start = std::chrono::steady_clock::now();
  };

};

inline CadicalSolver::TimeoutTerminator::TimeoutTerminator(double max_runtime) : max_runtime(max_runtime) {
}

inline bool CadicalSolver::TimeoutTerminator::terminate() {
  auto current_time = std::chrono::steady_clock::now();
  std::chrono::duration<double> elapsed_seconds = current_time - start;
  return elapsed_seconds.count() > max_runtime;
}

inline CadicalSolver::~CadicalSolver() {
  // TODO: do we really need this? If the solver is in an invalid state we cannot disconnect the terminator.
  // solver.disconnect_terminator();
}

inline void CadicalSolver::appendFormula(const std::vector<Clause>& formula) {
  for (auto& clause: formula) {
    addClause(clause);
  }
}


inline void CadicalSolver::addClause(const Clause& clause) {
  for (auto& l: clause) {
    solver.add(l);
  }
  solver.add(0);
}

inline void CadicalSolver::addClause(Clause&& clause) {
  for (auto& l: clause) {
    solver.add(l);
  }
  solver.add(0);
}

inline void CadicalSolver::addCombinedClause(const Clause& cl1, const Clause& cl2, const Clause& cl3) {
  for (auto& l: cl1) {
    solver.add(l);
  }
  for (auto& l: cl2) {
    solver.add(l);
  }
  for (auto& l: cl3) {
    solver.add(l);
  }
  solver.add(0);
}

inline void CadicalSolver::addCombinedClause(const Clause& cl1, const Clause& cl2, Clause&& cl3) {
  for (auto& l: cl1) {
    solver.add(l);
  }
  for (auto& l: cl2) {
    solver.add(l);
  }
  for (auto& l: cl3) {
    solver.add(l);
  }
  solver.add(0);
}

inline void CadicalSolver::assume(const std::vector<int>& assumptions) {
  for (auto& l: assumptions) {
    solver.assume(l);
  }
}

inline void CadicalSolver::assume(std::vector<int>&& assumptions) {
  for (auto& l: assumptions) {
    solver.assume(l);
  }
}

inline void CadicalSolver::assumeAll(const std::vector<int>& assumptions) {
  solver.reset_assumptions();
  assume(assumptions);
}

inline int CadicalSolver::solve(double timeout, const std::vector<int>& assumptions) {
  assumeAll(assumptions);
  std::chrono::time_point<std::chrono::steady_clock> start = std::chrono::steady_clock::now();
  TimeoutTerminator terminator(timeout);
  solver.connect_terminator(&terminator);
  int status = solver.solve();
  last_runtime = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now() - start).count();
  if (solver.state() == CaDiCaL::INVALID) {
    std::cerr<<"Solver is in invalid state"<<std::endl;
    return -1;
  }
  solver.disconnect_terminator();
  return status;
}

inline int CadicalSolver::solve(const std::vector<int>& assumptions) {
  assumeAll(assumptions);
  std::chrono::time_point<std::chrono::steady_clock> start = std::chrono::steady_clock::now();
  int status = solver.solve();
  last_runtime = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now() - start).count();
  return status;
}

inline int CadicalSolver::solve() {
  std::chrono::time_point<std::chrono::steady_clock> start = std::chrono::steady_clock::now();
  int status = solver.solve();
  last_runtime = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now() - start).count();
  return status;
}

inline double CadicalSolver::getRunTime() const {
  return last_runtime;
}

inline std::vector<int> CadicalSolver::getFailed(const std::vector<int>& assumptions) {
  std::vector<int> failed_literals;
  for (auto& l: assumptions) {
    if (solver.failed(l)) {
      failed_literals.push_back(l);
    }
  }
  return failed_literals;
}

inline std::vector<int> CadicalSolver::getValues(const std::vector<int>& variables) {
  std::vector<int> assignment;
  for (auto& v: variables) {
    assignment.push_back(val(v));
  }
  return assignment;
}

inline std::vector<int> CadicalSolver::getModel() {
  std::vector<int> assignment;
  for (int v = 1; v <= solver.vars(); v++) {
    assignment.push_back(val(v));
  }
  return assignment;
}


inline int CadicalSolver::val(int variable) {
  auto l = solver.val(variable);
  auto v = abs(l);
  if (v == variable) {
    return l;
  } else {
    return variable;
  }
}

// TODO:
inline bool CadicalSolver::isReady() const {
  return solver.state() != CaDiCaL::INVALID;
}

}

#endif // CADICAL_IPASIR_H_
