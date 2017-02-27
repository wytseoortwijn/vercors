VerCors Verification Toolset
=======

This repository hosts VerCors, a toolset for the verification of concurrent and parallel programs. VerCors aims to verify many different concurrency constructs, including: heterogeneous concurrency (Java and C), GPU kernels using barriers and atomics (OpenCL), and compiler directives as used in deterministic parallelism (OpenMP). VerCors is able to prove data-race freedom, memory safety, and functional correctness of (concurrent) programs written in Java, C, OpenCL, and OpenMP. Moreover, VerCors is designed to be language-independent, which makes adding new front-end languages a straightforward engineering effort.

Installation Instructions
-------------

The VerCors toolset can be installed and used on MacOS X, Linux, and Windows (via Cygwin). When using Windows make sure that the environment variable `JAVA_HOME` is configured. A basic installation requires:

- Java Development Kit (JDK), version 8
- Git (on Windows you need Git Bash, see https://git-scm.com/downloads)

All other dependencies are included in the repository and do not have to be installed for basic use of VerCors. However, if you aim to develop or extend VerCors the following dependencies need to be installed:

- Apache Ant 
- SBT

pre-requisites
-------------

For a basic installation of the VerCors toolset you need:

- Java version 7 or 8 JDK.
- Especically on Windows, the environment variable JAVA_HOME must be set. Without it, ant is unable to find the Java compiler.
- git (On Windows you need git bash, see https://git-scm.com/downloads).

Advanced installation topics are covered in the manual and the developers guide.

installation
------------

1. Open a new terminal window or git bash window.
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

