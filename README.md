# eSLIM

eSLIM is a tool for circuit minimization that utilizes <ins>**e**</ins>xact <ins>**s**</ins>ynthesis and the SAT-based local improvement method (<ins>**SLIM**</ins>) to locally improve circuits.


## Overview

The ***src*** directory contains the source code of the tool.


## Installation

### Dependencies

The following dependencies must be installed:
- [pybind11](https://github.com/pybind/pybind11)
- [bitarray](https://pypi.org/project/bitarray/)
- [CMake >= 3.4](https://cmake.org/)
- [GCC](https://gcc.gnu.org/)
- [python >= 3.7](https://www.python.org/)

To use the QBF-based minimization at least one of the following QBF solvers needs to be installed.
- [QFUN](https://sat.inesc-id.pt/~mikolas/sw/qfun/)
- [miniQU](https://github.com/fslivovsky/miniQU)
- [QuAbS](https://github.com/ltentrup/quabs)

We recommend using the solver ***QFUN***. 
In addition to installing a solver also the path to the binary needs to be set in ***utils.py***. 

### Optional Dependencies

To use [ABC](https://people.eecs.berkeley.edu/~alanmi/abc/) for inprocessing, the ***ABC*** synthesis and verification tool needs to be installed.
Additionally, the path to the ***ABC*** binary needs to be set in ***utils.py***. 

### Included Dependencies

To read and write AIGs (And-Inverter Graph) the [AIGER](https://github.com/arminbiere/aiger) library is used.
For checking SAT formulae the SAT solver [CaDiCaL](https://github.com/arminbiere/cadical) is used.

### Build

We only provide instructions for building the tool on a LINUX system.
```
git clone --recursive https://github.com/fxreichl/eSLIM.git synth
cd synth/bindings 
mkdir build && cd build
cmake ..
make
```

## Usage


To minimize a circuit use ***reduce.py***.
To run this script use:
```
reduce.py <Specification> <Result> <Limit>
```
#### Inputs

- ```Specification``` the circuit to minimize. Given either in the BLIF or in the AIGER format. If the BLIF format is used than the input must be sorted topologically, i.e., gates must be introduced before they are used. Note that not all current best implementations in the EPFL suite are sorted topologically.
- ```Result``` the file to which the resulting circuit shall be written. By default, the result is given as a BLIF. By using the options ***--aig*** and ***--aig-out*** the result can be given in the AIGER format (if the filename has the ***.aag*** extension the ASCII AIGER format is used otherwise the binary AIGER format is used).
- ```Limit``` the available time budget given in seconds.

#### Options

- ```--gs``` Number of inputs of the gates
- ```--aig``` Synthesise an AIG
- ```--abc``` Use ABC for inprocessing
- ```--restarts``` Number of restarts
- ```--syn-mode``` Specify if the QBF or the SAT-based approach shall be used
- ```--windows```Maximum number of windows and the reference size of the windows
- ```--size``` Initial bound for the subcircuits
- ```--fixed-size``` Disable fixed bounds
- ```--expansion``` Specify the expansion strategy


<!--

### Library Use

## How to Cite

## Contributors

-->

