#!/bin/bash

d=`echo $0 |sed 's/[^/]*$//' `
. $d/settings

export MOD_MAIN=/home/sccblom/sfw
export MOD_PATH=$MOD_MAIN
export MOD_MAKE_OPTS="-j 6"
. $MOD_MAIN/bin/mod_setup.sh

module purge
module load java/se7 mono/2.10.2 vercors/git

# ugly hack to invoke java with a -D flag, to use env var TEMPDIR
# this makes the cvt shell script use the shell script named  java
# from the bin subdiretory.
# that shell script invokes the real java program with the -D flag,
# in addition to the command line options with which it gets involved
PATH=$d/bin:$PATH

mkdir $tmppfx
cd $tmppfx


file=file.${LANGUAGE}
cat > $file

showencoded=
if [ X$SHOWENCODED != "X" ]
then
	#ln -s /dev/fd/1 encoded.chalice
	ln -s /dev/fd/$PUPTOL_VCT_ENCODED_FD encoded.chalice
	showencoded="--encoded=encoded.chalice"
fi

#echo "dovct $PATH" 1>&2
echo Invoking: vct $showencoded "$@" $file 1>&2
echo "" 1>&2
$PUPTOLROOT/bin/memtime -t 1 -o $PUPTOL_VCT_MEMTIME_FD -c 900 vct $showencoded "$@" $file


cd ..
rm -rf $tmppfx


