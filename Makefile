TIMEOUT = 20

EXTRACTED_FILES = \
    proof/jasmin_extracts/W64_SchnorrExtract.ec \
    proof/jasmin_extracts/W64_SchnorrExtract_ct.ec \
    proof/jasmin_extracts/ConstantsExtract.ec \
    proof/jasmin_extracts/ConstantsExtract_ct.ec

PROOF_FILES += $(EXTRACTED_FILES)
PROOF_FILES += $(wildcard proof/*.ec)
PROOF_FILES += $(wildcard proof/schnorr_protocol/*.ec)
PROOF_FILES += $(wildcard proof/modular_multiplication/*.ec)
PROOF_FILES += $(wildcard proof/montgomery_ladder/*.ec)
PROOF_FILES += $(wildcard proof/rejection_sampling/*.ec)
PROOF_FILES += $(wildcard proof/finite_types/*.ec)
PROOF_FILES += $(wildcard proof/definition_analysis/*.ec)


JASMIN_PROGNAME = jasminc
EASYCRYPT_PROGNAME = easycrypt


EASYCRYPT_REVISION = 94538c5
JASMIN_VERSION = 2022.09.2
BIGNUM_REVISION = e5c3a1e
EASYCRYPT_ZK_REVISION = 4a99a0f

.DELETE_ON_ERROR :

default : check_all

# Check all EasyCrypt proofs
check_all : $(PROOF_FILES:.ec=.eco)

extract_all : $(EXTRACTED_FILES)

# Use the tested EasyCrypt and Jasmin version in opam
# Requirements in Arch: sudo pacman -S z3 cvc4 pkg-config gmp pcre zlib mpfr ppl autoconf
# Requirements in Ubuntu: sudo apt install opam cvc4 pkg-config libgmp-dev libpcre3-dev zlib1g-dev libmpfr-dev libppl-dev autoconf python3-distutils
# Current versioon of `apron` fails to build on newer systems. Temporary workaround: opam pin add apron --dev-repo
opam_pin :
	opam update
	opam pin add easycrypt https://github.com/EasyCrypt/easycrypt.git#$(EASYCRYPT_REVISION)
	opam install easycrypt jasmin.$(JASMIN_VERSION) alt-ergo
	why3 config detect

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
	wget https://github.com/dfirsov/easycrypt-zk-code/archive/$(EASYCRYPT_ZK_REVISION).zip -O tmp/easycrypt-zk-code.zip
	unzip tmp/easycrypt-zk-code.zip -d tmp/zk_unpack

	mkdir -p proof/eclib
	cp tmp/unpack-jasmin/*/eclib/*.ec proof/eclib/
	cp tmp/unpack-bignum/*/proof/eclib_extra/JBigNum.ec proof/eclib/
# cp tmp/unpack-bignum/*/proof/eclib/JArray.ec proof/eclib/
	cp -a tmp/zk_unpack/easycrypt-zk-code-* easycrypt-zk-code


%.eco : %.ec $(PROOF_FILES)
	echo Checking "$<"
	easycrypt -p "CVC4" -p "Z3" -p "Alt-Ergo" -I ./proof -I Jasmin:./proof/eclib -I ./proof/jasmin_extracts -I ./proof/modular_multiplication -I ./proof/finite_types -I ./proof/montgomery_ladder -I ./proof/rejection_sampling -I ./proof/schnorr_protocol -I ./easycrypt-zk-code/generic -I ./easycrypt-zk-code/rewinding -I ./easycrypt-zk-code/misc -timeout "$(TIMEOUT)" "$<" 

# Check all EasyCrypt files from Jasmin sources
# If you do not have Jasmin, you can remove this block to skip extraction
extract_all $(EXTRACTED_FILES) : src/schnorr_protocol.jazz src/constants.jazz Makefile
	rm -rf proof/jasmin_extracts
	mkdir proof/jasmin_extracts
	$(JASMIN_PROGNAME)     -ec addm2 -ec commitment -ec response -ec challenge -ec verify -oec proof/jasmin_extracts/W64_SchnorrExtract.ec    -oecarray proof/jasmin_extracts src/schnorr_protocol.jazz
	$(JASMIN_PROGNAME) -CT -ec commitment -ec response -ec challenge -ec verify -oec proof/jasmin_extracts/W64_SchnorrExtract_ct.ec -oecarray proof/jasmin_extracts src/schnorr_protocol.jazz
	$(JASMIN_PROGNAME)     -ec bn_set_p -ec bn_set_q -ec bn_set_g -ec bn_set_bp -ec bn_set_bq -oec proof/jasmin_extracts/ConstantsExtract.ec      -oecarray proof/jasmin_extracts src/constants.jazz
	$(JASMIN_PROGNAME) -CT -ec bn_set_p -ec bn_set_q -ec bn_set_g -ec bn_set_bp -ec bn_set_bq -oec proof/jasmin_extracts/ConstantsExtract_ct.ec   -oecarray proof/jasmin_extracts src/constants.jazz

src/constants.jazz : src/constants.py
	make -C src constants.jazz
