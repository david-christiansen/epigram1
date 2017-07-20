################################################################################
# Epigram: src Makefile
################################################################################


########################################
# Variable Settings
# these are defaults which are over-ridden by cmd-line settings (or env vars)

OPT = -O

PROF = 

WHERE = .

# NB this should just be an executable name, indicating which vsn of ghc to use

GHC = ghc

# use GHC_EXTRA_PREFS to add your own preferred options, eg -dshow-passes
GHC_EXTRA_PREFS = 



########################################
# Common settings
#  - we shouldn't really modify these

FIXED_FLAGS = -package lang -fglasgow-exts \
		-fallow-overlapping-instances \
		-fallow-undecidable-instances 

####################################################
#for ghc 6.5 use these flags instead 
#FIXED_FLAGS =   -fglasgow-exts \
#		-fallow-overlapping-instances \
#		-fallow-undecidable-instances 
####################################################

PROF_OPTIONS = -prof -auto-all -auto-dicts -caf-all


########################################
# Constructed settings
#  - built from pieces above.

BUILD_PLACES = -odir${WHERE} -i -i${WHERE} -hidir${WHERE} 

GHC_ALL = ${GHC} ${FIXED_FLAGS} ${OPT} ${PROF} \
		${BUILD_PLACES} ${GHC_EXTRA_PREFS} 

GHC_BASE = ${shell which ${GHC} | perl -pe 's/bin.*//;s{/cygdrive/c}{c:};'}




########################################
# main targets

the_epigram : emacs-files
	if [ ! -r ${WHERE} ]; then mkdir ${WHERE}; fi
	${GHC_ALL} --make Main.lhs -optl-s -o ${WHERE}/Epigram-bin

ghci_epigram : emacs-files
	${GHC}i ${FIXED_FLAGS} ${OPT} Main.lhs


#################
# possible - namings based on option combinations? 
# but possibly ok for just the binary, to make sure.
# want to have the time/date stamping too? for version control? 
# note: these build names are used by testing.

# IMPORTANT: if you want remake_builds to work, use the same names!

# for completeness, make with the standard options but put in build/std
std :
	make WHERE="../build/std"

# optimisation turned off.
plain :
	make OPT= -Onot \
		WHERE="../build/plain"

opt :
	make OPT=-O \
		WHERE="../build/opt"

very_opt :
	# want other tricks too? 
	make OPT="-O2 -fvia-C" \
		WHERE="../build/very_opt"

prof : 
	make PROF="${PROF_OPTIONS}" \
		WHERE="../build/prof"

prof_opt : 
	make PROF="${PROF_OPTIONS}" OPT=-O \
		WHERE="../build/prof_opt"


####################
# note: this only targets your current builds
remake_builds :
	make prof_hacks
	for f in ../build/*; do echo remaking $$f; make `basename $$f`; done

all_builds : 
	make std prof prof_opt opt very_opt



########################################
# workarounds or special cases 

prof_hacks :
	make prof_hack_Equality prof_hack_Unify prof_hack_Elab \
		WHERE="../build/prof_opt" \
		PROF="${PROF_OPTIONS}" OPT=-O
	make prof_opt

prof_hack_Equality : 
	make prof_hack WHICH=Equality
prof_hack_Unify :
	make prof_hack WHICH=Unify
prof_hack_Elab :
	make prof_hack WHICH=Elab

prof_hack : 
	# full make up to here, just in case 
	- ${GHC_ALL} --make ${WHICH}.lhs 
	${GHC_ALL}   -C     ${WHICH}.lhs -o ${WHERE}/${WHICH}.hc
	perl -i -ne 'if (/CCS_DECLARE.*sat_CAF_cc_ccs/) { print if ! $$seen++;} else { print; }' ${WHERE}/${WHICH}.hc
	${GHC_ALL} -c ${WHERE}/${WHICH}.hc 



################################################################################
# extras

####################
# various files needed for emacs (eg byte compilations)

EMACS_QUOTE_FILE = ${shell if [ -r /usr/bin/sun ]; then echo '\"emacs-epigram.el\"'; else echo '"emacs-epigram.el"'; fi}

emacs-files : emacs-epigram.elc

emacs-epigram.elc : emacs-epigram.el
	xemacs -batch -eval '(byte-compile-file ${EMACS_QUOTE_FILE})' -kill


####################
# moving current build to epigram-binaries repository
# assumes that this is checked out parallel to the current distribution.
# assumes binary is already added to the repository
# NB only does check in in specific dirs, to avoid downloading other binaries
# compresses the windows version before sending - I've only got dial-up!

BINARY_REPOSITORY = ../../epigram-binaries

lx_bin : the_epigram
	cp Epigram-bin ${BINARY_REPOSITORY}/linux
	cd ${BINARY_REPOSITORY}/linux && cvs ci -m "new linux binary"

# the windows version forces a cvs update - to ensure up-to-date build
xp_bin : 
	cvs update
	make the_epigram
	bzip2 -k Epigram-bin.exe 
	mv Epigram-bin.exe.bz2 ${BINARY_REPOSITORY}/windows
	cd ${BINARY_REPOSITORY}/windows && cvs ci -m "new windows binary" Epigram-bin.exe.bz2
	

	
	

####################
# module interfaces etc in html, via haddock
# NOTE: this relies on a hacked version of haddock, on account of non-98 code

html :
	${GHC} -E -keep-tmp-files *.lhs
	perl -ni -e 'print unless /^#/;' *.hspp
	perl -pi -e 's/\(n\+1\)/n/g;' Zip.hspp		# special case, but why?
	- # note: might want to include other .haddock files from ghc doc dist
	haddock --html \
		--title='Epigram source code' 	\
		--prologue=../doc/html-blurb	\
		--gen-contents --gen-index	\
		--odir=../doc/html 		\
		 -i ${GHC_BASE}/doc/html/libraries/base/base.haddock \
		*hspp
	rm -rf *hspp *hspp.bak



####################
# for making standard packages for distribution

dist : 
	# perhaps should do this in main Makefile?


####################
# this (re-) creates the text at the end of this file.
# --make might occasionally make mistakes, just be aware...

deps :
	${GHC_ALL} -M *.lhs




################################################################################
# DO NOT DELETE: Beginning of Haskell dependencies
# DO NOT DELETE: End of Haskell dependencies
