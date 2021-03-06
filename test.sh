#!/bin/bash

#set -x
export LLVM_HOME=usr/lib/llvm-12

ARGS=`python3 ./HandleArgs.py $@`

[ "$ARGS" ] || exit 1

if [[ ${#ARGS} -gt 200 ]]; then
    python3 ./HandleArgs.py $@
    exit 1
fi

# convert string to array
ARG=(`echo ${ARGS}`);

FOO_VAR=''


for (( Idx=0; Idx<${#ARG[@]}; Idx++ ))
do
	#echo "${ARG[$Idx]}"
	FOO_VAR="${FOO_VAR}""-D"${ARG[$Idx]}';'
	
done


FOO_VAR=`echo $FOO_VAR | sed -e 's/;$//g'`
echo "$FOO_VAR"
export FOO_VAR

#clang++-11 -S -emit-llvm All_Testcases/9.cpp -o test.ll
#opt-11 -S -instnamer test.ll -o test.ll
mkdir -p build
pushd build
cmake -DCMAKE_CXX_FLAGS="-pg" -DCMAKE_EXE_LINKER_FLAGS=-pg ..
make
popd
clang-12 -S -emit-llvm -O0 -Xclang -disable-O0-optnone -fno-discard-value-names -c ex1.c -o test.ll
opt-12 -S -instnamer -mem2reg test.ll -o test.ll
./build/VascoLfcpaPass/VascoLfcpaPass ./SPEC/gobmk.ll
#clang++-11 -S -emit-llvm -O0 -Xclang -disable-O0-optnone -c All_Testcases/7.cpp -o test.ll
#opt-11 -S -instnamer -mem2reg -load /usr/local/lib/libSpatial.so -load  _build/*/*TransformIR*  -lfcpa test.ll -o test.ll #> /dev/null
#opt-11 -S -instnamer -mem2reg -load /usr/local/lib/libSpatial.so -load  _build/*/*TransformIR*  -lfcpa /home/aditi/rebenchmarktesting/Aditi/gcc.ll -o test.ll
#opt-11 -S  -instnamer -mem2reg -load /usr/local/lib/libSpatial.so -load  _build/*/*TransformIR*  -lfcpa phi_gep_br_bb_ptr.ll -o test.ll 
