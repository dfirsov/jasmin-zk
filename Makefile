TIMEOUT = 20

EXTRACTED_FILES = proof/jasmin_extracts/W64_SchnorrExtract.ec proof/jasmin_extracts/W64_SchnorrExtract_ct.ec

PROOF_FILES += $(EXTRACTED_FILES)
PROOF_FILES += $(wildcard proof/*)
PROOF_FILES += $(wildcard proof/modular_multiplication/*)
PROOF_FILES += $(wildcard proof/montgomery_ladder/*)
PROOF_FILES += $(wildcard proof/rejection_sampling/*)
PROOF_FILES += $(wildcard proof/schnorr_protocol/*)
PROOF_FILES += $(wildcard proof/definition_analysis/*)


JASMIN_PROGNAME = jasminc
EASYCRYPT_PROGNAME = easycrypt

EASYCRYPT_REVISION = r2022.04
JASMIN_VERSION = 2022.09.2
BIGNUM_REVISION = 81639ae

.DELETE_ON_ERROR :

default : check_all

# Check all EasyCrypt proofs
check_all : $(PROOF_FILES:.ec=.eco)

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
	rm -rf easycrypt-zk-code/
	mkdir tmp
	wget https://github.com/jasmin-lang/jasmin/archive/refs/tags/v$(JASMIN_VERSION).zip -O tmp/jasmin_archive.zip
	unzip tmp/jasmin_archive.zip -d tmp/unpack-jasmin
	wget https://github.com/formosa-crypto/libjbn/archive/$(BIGNUM_REVISION).zip -O tmp/bignum_archive.zip
	unzip tmp/bignum_archive.zip -d tmp/unpack-bignum
	wget https://github.com/dfirsov/easycrypt-zk-code/archive/refs/heads/main.zip -O tmp/easycrypt-zk-code.zip
	unzip tmp/easycrypt-zk-code.zip -d tmp/zk_unpack

	mkdir -p proof/eclib
	cp tmp/unpack-jasmin/*/eclib/*.ec proof/eclib/
	cp tmp/unpack-bignum/*/proof/eclib_extra/JBigNum.ec proof/eclib/
	cp tmp/unpack-bignum/*/proof/eclib/JArray.ec proof/eclib/
	cp -a tmp/zk_unpack/easycrypt-zk-code-main easycrypt-zk-code


%.eco : %.ec $(PROOF_FILES)
	echo Checking "$<"
	easycrypt -p "CVC4" -p "Z3" -p "Alt-Ergo" -I ./proof -I Jasmin:./proof/eclib -I ./proof/jasmin_extracts -I ./proof/modular_multiplication -I ./proof/montgomery_ladder -I ./proof/rejection_sampling -I ./proof/schnorr_protocol -I ./easycrypt-zk-code/generic -I ./easycrypt-zk-code/rewinding -I ./easycrypt-zk-code/misc -timeout "$(TIMEOUT)" "$<" 

# If you do not have Jasmin, you can remove this block to skip extraction
proof/jasmin_extracts/W64_SchnorrExtract.ec proof/jasmin_extracts/W64_SchnorrExtract_ct.ec : src/schnorr_protocol.jazz Makefile
	rm -rf proof/jasmin_extracts
	mkdir proof/jasmin_extracts
	$(JASMIN_PROGNAME) -ec commitment -ec response -ec challenge -ec verify -oec $@ -oecarray proof/jasmin_extracts $<
	$(JASMIN_PROGNAME) -CT -ec commitment -ec response -ec challenge -ec verify -oec proof/jasmin_extracts/W64_SchnorrExtract_ct.ec -oecarray proof/jasmin_extracts $<


