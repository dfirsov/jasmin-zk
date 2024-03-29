TIMEOUT ?= 20

EXTRACTED_FILES = \
    proof/jasmin_extracts/W64_SchnorrExtract.ec \
    proof/jasmin_extracts/W64_SchnorrExtract_ct.ec

PROOF_FILES += $(EXTRACTED_FILES)
PROOF_FILES += $(wildcard proof/*.eca)
PROOF_FILES += $(wildcard proof/*.ec)
PROOF_FILES += $(wildcard proof/big_num_ops/*.ec)
PROOF_FILES += $(wildcard proof/big_num_ops/*.eca)
PROOF_FILES += $(wildcard proof/big_num_ops/leakage_freeness/*.ec)
PROOF_FILES += $(wildcard proof/definition_analysis/*.ec)
PROOF_FILES += $(wildcard proof/definition_analysis/*.eca)
PROOF_FILES += $(wildcard proof/modular_multiplication/*.ec)
PROOF_FILES += $(wildcard proof/modular_multiplication/*.eca)
PROOF_FILES += $(wildcard proof/modular_multiplication/leakage_freeness/*.ec)
PROOF_FILES += $(wildcard proof/montgomery_ladder/*.ec)
PROOF_FILES += $(wildcard proof/montgomery_ladder/*.eca)
PROOF_FILES += $(wildcard proof/montgomery_ladder/leakage_freeness/*.ec)
PROOF_FILES += $(wildcard proof/random_bit/*.ec)
PROOF_FILES += $(wildcard proof/random_bit/*.eca)
PROOF_FILES += $(wildcard proof/random_bit/leakage_freeness/*.ec)
PROOF_FILES += $(wildcard proof/rejection_sampling/*.ec)
PROOF_FILES += $(wildcard proof/rejection_sampling/*.eca)
PROOF_FILES += $(wildcard proof/rejection_sampling/leakage_freeness/*.ec)
PROOF_FILES += $(wildcard proof/schnorr_protocol/*.ec)
PROOF_FILES += $(wildcard proof/schnorr_protocol/*.eca)
PROOF_FILES += $(wildcard proof/schnorr_protocol/leakage_freeness/*.ec)
PROOF_FILES += $(wildcard proof/auxiliary_lemmas/*.ec)
PROOF_FILES += $(wildcard proof/auxiliary_lemmas/*.eca)


JASMIN ?= jasminc
EASYCRYPT ?= easycrypt
ECARGS ?=

EASYCRYPT_REVISION = 860dc3f
JASMIN_VERSION = 2022.09.3
BIGNUM_REVISION = e5c3a1e
EASYCRYPT_ZK_REVISION = 6d35e43

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
	cp -a tmp/zk_unpack/easycrypt-zk-code-* easycrypt-zk-code


%.eco : %.ec $(PROOF_FILES)
	echo Checking "$<"
	$(EASYCRYPT) $(ECARGS) -p "CVC4" -p "Z3" -p "Alt-Ergo" -I ./proof/auxiliary_lemmas -I ./proof/big_num_ops -I ./proof/big_num_ops/leakage_freeness  -I ./proof/random_bit -I ./proof/random_bit/leakage_freeness -I ./proof -I Jasmin:./proof/eclib  -I ./proof/jasmin_extracts -I ./proof/modular_multiplication -I ./proof/modular_multiplication/leakage_freeness  -I ./proof/montgomery_ladder -I ./proof/montgomery_ladder/leakage_freeness -I ./proof/rejection_sampling -I ./proof/rejection_sampling/leakage_freeness -I ./proof/schnorr_protocol -I ./proof/schnorr_protocol/leakage_freeness -I ./easycrypt-zk-code/generic -I ./easycrypt-zk-code/rewinding -I ./easycrypt-zk-code/misc -timeout "$(TIMEOUT)" "$<"

# Check all EasyCrypt files from Jasmin sources
# If you do not have Jasmin, you can remove this block to skip extraction
EXTRACTED_FUNCTIONS = -ec random_bit_naive -ec random_bit -ec uniform_binary_choice -ec bn_addm2 -ec cminusP -ec challenge_indexed -ec commitment_indexed -ec usample -ec bn_cmov -ec bn_addc -ec commitment -ec response -ec challenge -ec verify -ec bn_set_ex_w -ec bn_set_ex_s
extract_all $(EXTRACTED_FILES) : src/schnorr_protocol.jazz src/constants.jazz Makefile
	rm -rf proof/jasmin_extracts
	mkdir proof/jasmin_extracts
	$(JASMIN)     $(EXTRACTED_FUNCTIONS) -oec proof/jasmin_extracts/W64_SchnorrExtract.ec    -oecarray proof/jasmin_extracts src/schnorr_protocol.jazz
	$(JASMIN) -CT $(EXTRACTED_FUNCTIONS) -oec proof/jasmin_extracts/W64_SchnorrExtract_ct.ec -oecarray proof/jasmin_extracts src/schnorr_protocol.jazz
	$(JASMIN) -safety $(EXTRACTED_FUNCTIONS) -oec proof/jasmin_extracts/W64_SchnorrExtract_mem.ec -oecarray proof/jasmin_extracts src/schnorr_protocol.jazz

src/constants.jazz : src/constants.py
	make -C src constants.jazz


compile_and_run :
	$(info This might take a while...)
	make -C src/example run



