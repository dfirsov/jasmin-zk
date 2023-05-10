
TIMEOUT = 20

ECO=
#ECO=-no-eco

# TODO: Add more
EXTRACTED_FILES = proof/jasmin_extracts/W64_SchnorrExtract.ec

# TODO: Add other directories
PROOF_FILES += $(EXTRACTED_FILES)
PROOF_FILES += $(wildcard proof/montgomery_ladder/*)

# Replace by "JASMIN_PROGNAME = echo jasmin" to deactivate extraction if you do not have jasmin installed
JASMIN_PROGNAME = jasminc
EASYCRYPT_PROGNAME = easycrypt

EASYCRYPT_REVISION = 94538c5
JASMIN_VERSION = 2022.09.2
BIGNUM_REVISION = 81639ae

.DELETE_ON_ERROR :

default : check_all

# Check all EasyCrypt proofs
check_all : $(PROOF_FILES:.ec=.check.log)

# Check all EasyCrypt files from Jasmin sources
extract_all : $(EXTRACTED_FILES)

# Use the tested EasyCrypt and Jasmin version in opam
opam_pin :
	opam update
	opam pin add easycrypt https://github.com/EasyCrypt/easycrypt.git#$(EASYCRYPT_REVISION)
	opam install easycrypt jasmin.$(JASMIN_VERSION)

# Downloads files in eclib
update_downloads :
	rm -rf tmp/
	rm -rf proof/eclib/
	mkdir tmp
	wget https://github.com/jasmin-lang/jasmin/archive/refs/tags/v$(JASMIN_VERSION).zip -O tmp/jasmin_archive.zip
	unzip tmp/jasmin_archive.zip -d tmp/unpack
	wget https://raw.githubusercontent.com/formosa-crypto/libjbn/$(BIGNUM_REVISION)/proof/eclib/JBigNum.ec -O tmp/JBigNum.ec
	cp -a tmp/unpack/*/eclib/ proof/
	cp tmp/JBigNum.ec proof/eclib

%.check.log : %.ec $(PROOF_FILES)
	echo Checking "$<"
	easycrypt $(ECO) -p "CVC4" -p "Z3" -p "Alt-Ergo" -I ./proof -I ./proof/eclib -I ./proof/montgomery_ladder -I ./proof/rejection_sampling -I ./proof/schnorr -timeout "$(TIMEOUT)" "$<" > $@

proof/jasmin_extracts/W64_SchnorrExtract.ec : src/schnorr_protocol.jazz Makefile
	$(JASMIN_PROGNAME) -ec commitment -ec response -ec challenge -ec verify -oec $@ -oecarray proof/jasmin_extracts $<


# BELOW: Experiments...


# opam pin add jasmin https://github.com/jasmin-lang/jasmin.git
# opam pin add easycrypt https://github.com/EasyCrypt/easycrypt.git
check_versions :
	EC_REVISION="`easycrypt config |& grep git-hash | cut -f 2 -d ' '`"; \
	echo "==== Easycrypt revision: $$EC_REVISION ===="; \
	if [ "$$EC_REVISION" != "$(EASYCRYPT_REVISION)" ]; then \
		echo "**********************************************************************************"; \
		echo "****** These files were tested with EasyCrypt revision $(EASYCRYPT_REVISION) *****"; \
		echo "**********************************************************************************"; \
	fi

