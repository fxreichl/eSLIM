#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include <vector>

#include "cadical.h"

namespace py = pybind11;

PYBIND11_MODULE(cadical, m) {
    py::class_<circuit_synthesis::CadicalSolver>(m, "Cadical")
        .def(py::init<>())
        .def("append_formula", &circuit_synthesis::CadicalSolver::appendFormula)
        .def("add_clause", py::overload_cast<const std::vector<int>&>(&circuit_synthesis::CadicalSolver::addClause))
        .def("solve", py::overload_cast<const std::vector<int>&>(&circuit_synthesis::CadicalSolver::solve))
        .def("solve_limited", py::overload_cast<double, const std::vector<int>&>(&circuit_synthesis::CadicalSolver::solve))
        .def("get_failed", &circuit_synthesis::CadicalSolver::getFailed)
        // .def("get_core", &circuit_synthesis::CadicalSolver::getCore)
        .def("get_values", &circuit_synthesis::CadicalSolver::getValues)
        .def("get_model", &circuit_synthesis::CadicalSolver::getModel)
        .def("get_runtime", &circuit_synthesis::CadicalSolver::getRunTime);
}


