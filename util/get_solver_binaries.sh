#!/bin/bash

# These are not necessarily the latest solver binaries
# This file's primary purpose is to facilitate testing on Travis

solver_dirs=(cvc4 z3 boolector)

echo "Scanning for solvers"

all_logic_solvers=true

for solver_dir in "${solver_dirs[@]}"
do
    if [ ! -d "`pwd`/smt_solvers/$solver_dir" ]; then
        echo "Missing at least $solver_dir and possibly more"
        echo "Retrieving solvers"
        rm -rf ./smt_solvers
        wget http://web.stanford.edu/~makaim/files/smt_solvers_fp.tar.gz
        tar -xzvf ./smt_solvers_fp.tar.gz
        all_logic_solvers=false
        break
    fi
done

if $all_logic_solvers; then
    echo "Found all solvers"
fi

echo "Adding paths to solvers"

export PYTHONPATH=$PYTHONPATH:`pwd`/smt_solvers/cvc4
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:`pwd`/smt_solvers/cvc4

export PATH=$PATH:`pwd`/smt_solvers/z3/bin/
export PYTHONPATH=$PYTHONPATH:`pwd`/smt_solvers/z3/bin/python/
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:`pwd`/smt_solvers/z3/bin

export PYTHONPATH=$PYTHONPATH:`pwd`/smt_solvers/boolector
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:`pwd`/smt_solvers/boolector
