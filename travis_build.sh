#!/bin/sh
# Script that is used in order to allow Travis 
# to link the Viper modules and build the tool.

# Link Viper modules
# Configure Carbon
cd vercors/viper/carbon
if [ -d "silver" ]
then
	# Erroneous directory
	rm -rf silver
fi
if ! [ -L "silver" ] 
then
	ln -s ../silver silver
fi
# Configure Silicon
cd ../silicon
if [ -d "silver" ] 
then
	# Erroneous directory
	rm -rf silver
fi
if ! [ -L "silver" ] 
then
	ln -s ../silver silver
fi
# Return to root directory
cd ../../..

# Compile the toolset
ant compile
