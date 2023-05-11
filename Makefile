TIMEOUT = 20

ECO=
#ECO=-no-eco

# TODO: Add more
EXTRACTED_FILES = proof/jasmin_extracts/W64_SchnorrExtract.ec

# TODO: Add other directories
PROOF_FILES += $(EXTRACTED_FILES)
PROOF_FILES += $(wildcard proof/schnorr_protocol/*)
PROOF_FILES += $(wildcard proof/*)
PROOF_FILES += $(wildcard proof/modular_multiplication/*)
PROOF_FILES += $(wildcard proof/montgomery_ladder/*)
PROOF_FILES += $(wildcard proof/rejection_sampling/*)



# Replace by "JASMIN_PROGNAME = echo jasmin" to deactivate extraction if you do not have jasmin installed
JASMIN_PROGNAME = jasminc
EASYCRYPT_PROGNAME = easycrypt

EASYCRYPT_REVISION = 577c882 # this is the latest released version with tag "r2022.04"
jasmin_VERSION = 2022.09.2
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
	wget https://raw.githubusercontent.com/formosa-crypto/libjbn/$(BIGNUM_REVISION)/proof/eclib_extra/JBigNum.ec -O tmp/JBigNum.ec
	wget https://raw.githubusercontent.com/formosa-crypto/libjbn/$(BIGNUM_REVISION)/proof/eclib/JArray.ec -O tmp/JArray.ec
	cp -a tmp/unpack/*/eclib/ proof/
	cp tmp/JBigNum.ec proof/eclib
	cp tmp/JArray.ec proof/eclib


%.check.log : %.ec $(PROOF_FILES)
	echo Checking "$<"
	easycrypt $(ECO) -p "CVC4" -p "Z3" -p "Alt-Ergo" -I ./proof -I ./proof/eclib -I ./proof/jasmin_extracts -I ./proof/modular_multiplication -I ./proof/montgomery_ladder -I ./proof/rejection_sampling -I ./proof/schnorr_protocol -I ./easycrypt-zk-code/generic -I ./easycrypt-zk-code/rewinding -I ./easycrypt-zk-code/misc -timeout "$(TIMEOUT)" "$<" 

### > $@

proof/jasmin_extracts/W64_SchnorrExtract.ec : src/schnorr_protocol.jazz Makefile
	rm -rf proof/jasmin_extracts
	mkdir proof/jasmin_extracts
	$(JASMIN_PROGNAME) -ec commitment -ec response -ec challenge -ec verify -oec $@ -oecarray proof/jasmin_extracts $<
	$(JASMIN_PROGNAME) -CT -ec commitment -ec response -ec challenge -ec verify -oec proof/jasmin_extracts/W64_SchnorrExtract_ct.ec -oecarray proof/jasmin_extracts $<



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

