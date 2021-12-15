PATH2LIB=~/Proj/Superblock/build/Superblock/LLVMSB.so        # Specify your build directory in the project
PASS=-psbpass                  # Choose either -fplicm-correctness or -fplicm-performance

# Delete outputs from previous run.
rm -f default.profraw ${1}_prof ${1}_psb ${1}_rsb ${1}_no_sb *.bc ${1}.profdata *_output *.ll

# Convert source code to bitcode (IR)
clang -emit-llvm -c ${1}.c -o ${1}.bc
# clang -emit-llvm -c ${1}.c -o ${1}.ls.bc

# Proj: Mem2reg
opt -mem2reg ${1}.bc -o ${1}.mr.bc

# Canonicalize natural loops
opt -loop-simplify ${1}.mr.bc -o ${1}.ls.bc

# Proj: Add LICM 
opt -licm ${1}.ls.bc -o ${1}.licm.bc
# Proj: Add Dead Code Elimination
opt -dce ${1}.licm.bc -o ${1}.dce.bc

# Instrument profiler
opt -pgo-instr-gen -instrprof ${1}.ls.bc -o ${1}.ls.prof.bc
# Generate binary executable with profiler embedded
clang -fprofile-instr-generate ${1}.ls.prof.bc -o ${1}_prof

# Generate profiled data
./${1}_prof > correct_output
llvm-profdata merge -o ${1}.profdata default.profraw

# Apply Superblock
opt -o ${1}.psb.bc -pgo-instr-use -pgo-test-profile-file=${1}.profdata -load ${PATH2LIB} -psbpass < ${1}.ls.bc > /dev/null
opt -o ${1}.rsb.bc -pgo-instr-use -pgo-test-profile-file=${1}.profdata -load ${PATH2LIB} -rsbpass < ${1}.ls.bc > /dev/null

# Proj: Add LICM 
opt -licm ${1}.psb.bc -o ${1}.psbl.bc
opt -licm ${1}.rsb.bc -o ${1}.rsbl.bc
# Proj: Add Dead Code Elimination
opt -dce ${1}.psbl.bc -o ${1}.psbo.bc
opt -dce ${1}.rsbl.bc -o ${1}.rsbo.bc

# Generate binary excutable before SuperBlock formation: Unoptimzied code
clang ${1}.dce.bc -o ${1}_no_sbo
clang ${1}.ls.bc -o ${1}_no_sb
# Generate binary executable after Profile SuperBlock: Optimized code
clang ${1}.psbo.bc -o ${1}_psbo
clang ${1}.psb.bc -o ${1}_psb
# Generate binary executable after Random SuperBlock: Comparison code
clang ${1}.rsbo.bc -o ${1}_rsbo
clang ${1}.rsb.bc -o ${1}_rsb

# Produce output from binary to check correctness
echo -e "Input: ${INPUT}\n"
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
    echo -e "1a. Performance of No-Superblock code, unoptimized"
    time ./${1}_no_sb ${INPUT} > /dev/null
    echo -e "\n\n"
    echo -e "1b. Performance of No-Superblock code, optimized"
    time ./${1}_no_sbo ${INPUT} > /dev/null
    echo -e "\n\n"
    echo -e "2a. Performance of Random Superblock code, unoptimized"
    time ./${1}_rsb ${INPUT} > /dev/null
    echo -e "\n\n"
    echo -e "2b. Performance of Random Superblock code, optimized"
    time ./${1}_rsbo ${INPUT} > /dev/null
    echo -e "\n\n"
    echo -e "3a. Performance of Profiled Superblock code, unoptimized"
    time ./${1}_psb ${INPUT} > /dev/null
    echo -e "\n\n"
    echo -e "3b. Performance of Profiled Superblock code, optimized"
    time ./${1}_psbo ${INPUT} > /dev/null
    echo -e "\n\n"
fi

# Cleanup
# rm -f default.profraw ${1}_prof ${1}_psb ${1}_no_sb *.bc ${1}.profdata *_output *.ll
