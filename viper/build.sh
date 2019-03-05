#!/bin/bash

(cd viper-api ; ant ) || (echo building viper API failed ; exit)

(cd silver ; sbt compile ) || (echo building silver failed ; exit)

(cd carbon ; sbt assembly ) || (echo building carbon failed ; exit)

(cd silicon ; sbt assembly ) || (echo building silicon failed ; exit)

echo build was succesful

