#!/bin/bash

clear

mkdir -p _build
pushd _build
make clean
cmake ..
make
popd

for FILE in ./SPEC/*.ll;
do
	echo -e "${REDB}==============================Running Analysis================================${REDB} \n"
	FILENAME=$(basename $FILE .ll)
	echo -e $FILENAME
	# if [[ $FILENAME == "sjeng" ]]; then
	# 	continue;
	# fi
	opt-12 -S -instnamer -mem2reg -time-passes -load /usr/local/lib/libSpatial.so -load  _build/*/*VascoLfcpa*  -lfcpa $FILE -o temp.ll
	rm temp.ll
	echo -e "\n"
	echo -e "${REDB}==============================Analysis Over================================${REDB} \n"
done

# echo -e "${REDB}==============================Running Analysis================================${REDB} \n"
# $DRIVER ./outputs/$FILENAME.ll
# echo -e "\n"
# echo -e "${REDB}==============================Analysis Over================================${REDB}"