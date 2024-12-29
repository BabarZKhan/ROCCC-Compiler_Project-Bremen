# ROCCC HLS Compiler-Project Bremen

While working on various other High-Level Synthesis (HLS) compilers, some years ago I have worked on Riverside Optimizing Compiler for Configurable Computing (ROCCC) High-Level Synthesis compiler as well for an academic research project [FDL2021](https://babarzkhan.github.io/publication/2021-09-09-FDL2021), and [DTA](https://babarzkhan.github.io/publication/2018-03-25). ROCCC is an open source compiler built upon the SUIF (Stanford University Intermediate Format) and Low Level Virtual Machine (LLVM) infrastructures. It raises the level of abstraction for programming FPGAs to a subset of C. My research goals revolved around the procedure level optimizations (passes) and loop level optimizations in the ROCCC HLS Compiler. The changes made in the original source code by me are released under the same original license.


This repository contains both the precompiled distributions, and the source code for the ROCCC project.

Using one of the precompiled distributions is the easiest way to install and use ROCCC. They can be found under the distributions/ folder. We provide 3:
   OS X     (Snow Leopard, Lion, Mountain Lion, Maverick)
   Ubuntu   (14.04 Trusty Tahr)
   CentOS   (5.x, 6.x)

   The source code can be found under the roccc-compiler/ folder, and the compilation steps are outlined in the INSTALL file. Installation from source has only been verified on OS X Snow Leopard, and CentOS 5.9, CentOS 5.11. 

   A CentOS 5.11 virtual machine has been created with ROCCC installed from source. It can be downloaded from:
   http://roccc.cs.ucr.edu/

   We recommend that users compile all ROCCC code through Eclipse with the provided plugin instead of through the command line. Source code for the plugin can be found under the eclipse-plugin/ folder, but the JAR files can be found in any precompiled distribution. The plugin requires a very specific setup in the ROCCC installation directory.  We recommend anybody wishing to compile from source to install a precompiled distribution in a separate folder. Then update its bin/ and lib/ folders with the compiled execution files, and object files. This will ensure the install directory is correctly setup.


----- ----- ----- ----- -----
KNOWN BUGS
----- ----- ----- ----- -----
   * The temporal common subexpression elimination (TCSE) has not been fully tested with other optimization. Usage may cause valid C code to not compile through ROCCC.



----- ----- ----- ----- -----
KNOWN BUGS
----- ----- ----- ----- -----
   * The temporal common subexpression elimination (TCSE) has not been fully tested with other optimization. Usage may cause valid C code to not compile through ROCCC.


