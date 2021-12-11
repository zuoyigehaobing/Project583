PATH2LIB=~/Proj/Superblock/build/Superblock/LLVMSB.so        # Specify your build directory in the project
PASS=-psbpass                  # Choose either -fplicm-correctness or -fplicm-performance

# Delete outputs from previous run.
rm -f default.profraw ${1}_prof ${1}_psb ${1}_rsb ${1}_no_sb *.bc ${1}.profdata *_output *.ll

##################        HW! setup        ##################
BENCH=src/${1}.c
INPUT=${2}

setup(){
if [[ ! -z "${INPUT}" ]]; then
echo "INPUT:${INPUT}"
ln -sf input1/${INPUT} .
fi
}

# Prepare input to run
setup
# Convert source code to bitcode (IR)
# This approach has an issue with -O2, so we are going to stick with default optimization level (-O0)
clang -emit-llvm -c ${BENCH} -o ${1}.bc 
# Instrument profiler
opt -pgo-instr-gen -instrprof ${1}.bc -o ${1}.prof.bc
# Generate binary executable with profiler embedded
# clang -fprofile-instr-generate ${1}.prof.bc -o ${1}.prof
clang -fprofile-instr-generate ${1}.prof.bc -o ${1}_prof


############# NOTE HW1 Format
# Collect profiling data
./${1}_prof ${INPUT} > correct_output

# Translate raw profiling data into LLVM data format
llvm-profdata merge -output=${1}.profdata default.profraw

# Prepare input to run
setup
# Apply your pass to bitcode (IR)
##################      end HW! setup      ##################
# Apply Superblock
opt -o ${1}.psb.bc -pgo-instr-use -pgo-test-profile-file=${1}.profdata -load ${PATH2LIB} -psbpass < ${1}.bc > /dev/null
opt -o ${1}.rsb.bc -pgo-instr-use -pgo-test-profile-file=${1}.profdata -load ${PATH2LIB} -rsbpass < ${1}.bc > /dev/null

# Generate binary excutable before SuperBlock formation: Unoptimzied code
clang ${1}.bc -o ${1}_no_sb
# Generate binary executable after Profile SuperBlock: Optimized code
clang ${1}.psb.bc -o ${1}_psb
# Generate binary executable after Profile SuperBlock: Comparison code
clang ${1}.rsb.bc -o ${1}_rsb

# Produce output from binary to check correctness
./${1}_psb ${INPUT} > psb_output
./${1}_rsb ${INPUT} > rsb_output

echo -e "\n=== Correctness Check ==="
if [ "$(diff correct_output psb_output)" != "" ]; then
    echo -e ">> PSB FAIL\n"
elif [ "$(diff correct_output rsb_output)" != "" ]; then
    echo -e ">> RSB FAIL\n" 
else
    echo -e ">> PASS\n"
    # Measure performance
    echo -e "1. Performance of unoptimized code"
    time ./${1}_no_sb ${INPUT} > /dev/null
    echo -e "\n\n"
    echo -e "2. Performance of Random Superblock code"
    time ./${1}_rsb ${INPUT} > /dev/null
    echo -e "\n\n"
    echo -e "2. Performance of Profiled SuperBlock code"
    time ./${1}_psb ${INPUT} > /dev/null
    echo -e "\n\n"
fi

# Cleanup
# rm -f default.profraw ${1}_prof ${1}_psb ${1}_no_sb *.bc ${1}.profdata *_output *.ll