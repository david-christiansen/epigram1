# Epigram 1

This is a version of Epigram 1, recovered from the Wayback Machine and
modified to build with current versions of GHC.

Current status: it builds using Stack, but the Elisp needs tweaking to
find the build product.

Tested on GNU/Linux, contributions and testing are welcome from Mac OS
and Windows users.

# Remaining Work

It would be convenient to get the interface to work with GNU Emacs

The current version here has not been thoroughly tested

It would be good to get it building with a few more systems in some
kind of CI as well.

# Installation Instructions

Run `stack install` to compile and install the Epigram binary, then run the `epigram` script in the project root to launch XEmacs and Epigram.
