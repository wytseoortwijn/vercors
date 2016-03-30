#!/bin/bash

(cd viper-api ; ant clean ) || (echo cleaning viper API failed ; exit)

(cd silver ; sbt clean ) || (echo cleaning silver failed ; exit)

(cd carbon ; sbt clean ) || (echo cleaning carbon failed ; exit)

(cd silicon ; sbt clean ) || (echo cleaning silicon failed ; exit)

echo clean was succesful

