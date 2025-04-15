##  Usage Guide

### 1. Install the `mcl` library

Clone the repository and build the library:

```bash
git clone https://github.com/herumi/mcl.git
cd mcl
make -j4
cd ..
```

Set the library path:

```bash
export LD_LIBRARY_PATH=./mcl/lib:$LD_LIBRARY_PATH
```

### 2. Compile the Code

Use the following command to compile:

```bash
g++ zkp_for_milp.cpp pcs.cpp timer.cpp -o zkp-milp \
    -I./mcl/include -I./head -L./mcl/lib \
    -lmcl -lgmp
```

### 3. Run the Demo

Once compiled, run the demo with:

```bash
./zkp-milp bbtree_result.txt
```
