VerCors
=======

This folder contains the VerCors tool set for
verification of concucrrent software as one complete bundle.


pre-requisites
-------------

For a basic installation of the VerCors toolset you need:

- Java version 7 or 8 JDK.
- git (On Windows you need git bash, see https://git-scm.com/downloads).
- for documentation only: pdflatex.

Advanced installation topics are covered in the manual and the developers guide.

installation
------------

1. Open a new terminal windows or git bash window.
2. cd to the directory where VerCors should be installed.
3. Issues the following commands

```
git clone https://github.com/utwente-fmt/vercors.git
cd vercors
./unix/bin/vct-ant
./unix/bin/vct --test=examples/manual --tool=silicon --lang=pvl,java
```

The last command should report that `all ??? tests passed`.

Optionally, you can build the documentation with the command
```
./unix/bin/vct-ant doc
```

