#!/bin/bash

echo -en "\\e[0Ktravis_fold:start:$1\\r"
echo -e "\\e[0K$2"

eval $3
code=$?

echo -en "travis_fold:end:$1\\r"

exit $code
