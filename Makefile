
TIMEOUT = 20

ECO=
#ECO=-no-eco

# TODO: Add more
EXTRACTED_FILES = proof/jasmin_extracts/Ring_ops_extract.ec proof/jasmin_extracts/Ring_ops_extract_ct.ec

# TODO: Add other directories
PROOF_FILES += $(EXTRACTED_FILES)
PROOF_FILES += $(wildcard proof/montgomery_ladder/*)

# Replace by "JASMIN_PROGNAME = echo jasmin" to deactivate extraction if you do not have jasmin installed
JASMIN_PROGNAME = jasminc
EASYCRYPT_PROGNAME = easycrypt

.DELETE_ON_ERROR :

default : check_all

%.check.log : %.ec $(PROOF_FILES)
	echo Checking "$<"
	easycrypt $(ECO) -p "CVC4" -p "Z3" -p "Alt-Ergo" -I ./proof -I ./proof/eclib -I ./proof/montgomery_ladder -I ./proof/rejection_sampling -I ./proof/schnorr -timeout "$(TIMEOUT)" "$<" > $@

# TODO
JASMIN_COMMAND = $(JASMIN_PROGNAME)

# TODO: Add for each Jazz extraction
proof/jasmin_extracts/Ring_ops_extract.ec : src/ring_ops.jazz
	# TODO proper syntax
	$(JASMIN_COMMAND) $< -o $@

proof/jasmin_extracts/Ring_ops_extract_ct.ec : src/ring_ops.jazz
	# TODO proper syntax
	$(JASMIN_COMMAND) $< -CT -o $@

check_all : $(PROOF_FILES:.ec=.check.log)

extract_all : $(EXTRACTED_FILES)


# BELOW: Experiments...

EASYCRYPT_REVISION = r2022.04-142-g94538c5
JASMIN_REVISION = abcdef

# opam pin add jasmin https://github.com/jasmin-lang/jasmin.git#
# opam pin add easycrypt https://github.com/EasyCrypt/easycrypt.git
check_versions :
	EC_REVISION="`easycrypt config |& grep git-hash | cut -f 2 -d ' '`"; \
	echo "==== Easycrypt revision: $$EC_REVISION ===="; \
	if [ "$$EC_REVISION" != "$(EASYCRYPT_REVISION)" ]; then \
		echo "**********************************************************************************"; \
		echo "****** These files were tested with EasyCrypt revision $(EASYCRYPT_REVISION) *****"; \
		echo "**********************************************************************************"; \
	fi

