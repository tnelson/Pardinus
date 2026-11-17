# Modified MiniSat-p

This is a version of MiniSat-p which has been frozen and modified to fix some issues. 

[Original](https://github.com/emina/minisatp), commit `7377e0bccf8bafcb4f3c4dcf108e51cdb3faa7de` from 2015. MIT Licensed.

## Local changes

* `Proof.C`, `File.C`: temporary proof log files are removed when the process ends. Previously, these had been removed only on process exit, which means that killing the solver process could leave (sometimes quite large) orphan files. 