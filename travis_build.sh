#!/bin/sh
# Script that is used in order to allow Travis 
# to link the Viper modules and build the tool.

# Link Viper modules
cd vercors/viper/carbon
ln -s ../silver silver
cd ../silicon
ln -s ../silver silver
cd ../../..

# Compile the toolset
ant compile
