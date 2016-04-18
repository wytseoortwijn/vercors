#!/bin/bash

# find out location of binary
DETECT=`dirname "$0"`
# parent is platform directory
DETECT=`dirname "$DETECT"`
# parent is home
export VCT_HOME=`dirname "$DETECT"`
export PATH=$VCT_HOME/unix/bin:$PATH

exec $VCT_HOME/deps/sbt/0.13.11/bin/sbt "$@"

