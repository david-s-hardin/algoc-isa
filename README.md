To build (if leg64.lisp is up-to-date):

{path-to-ACL2}/books/build/cert.pl --acl2 {acl2-executable-name} fact-leg64.lisp


To build the ACL2 file leg64.lisp, and the leg64.cert certified ACL2 proof book:

{path to ACL2}/books/projects/rac/bin/rac -a leg64.cpp


To build leg64 ISA simulator executable (using clang on MacOS)

cl+ -I{path to ACL2}/books/projects/rac/include -DCOMPILE_ME leg64.cpp -o leg64
