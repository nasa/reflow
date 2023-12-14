#!/bin/bash
[ ! -f $1 ] && echo "Error: $1 is not a file." && exit 1;
# These environment variables should be modified for each particular installation
FRAMAC_CMD="frama-c"
FRAMAC_WP_SHARE_FOLDER="/Users/ltitolo/Desktop/framac-why3-pvs/share/frama-c/wp"
ADHOC_WP_DRIVER="/Users/ltitolo/Desktop/framac-why3-pvs/share/frama-c/wp/wp-nasalib"
INPUT_FILE=$1

# No modifications should be necessary below this line

frama-c \
    -wp \
    -wp-timeout 0 \
    -wp-prover pvs \
    -wp-session $PWD \
    -wp-out $PWD \
    -wp-interactive edit \
    -wp-model Typed+float \
    -wp-driver $ADHOC_WP_DRIVER.driver \
    -wp-share $FRAMAC_WP_SHARE_FOLDER \
    $INPUT_FILE


if [ -d $PWD/"interactive" ]
then
    cd $PWD/interactive

    # The frama_c_wp_precisa/Interface.pvs file connects the
    # verification conditions with the PVS file that used as
    # input for PRECiSA. This connection is done manually for now.
    if [ ! -d frama_c_wp_precisa ]; then mkdir frama_c_wp_precisa; fi
    if [ ! -f "frama_c_wp_precisa/Interface.pvs" ]; then
	printf "%% Generated automatically by run-framac.sh\n%%\nInterface: THEORY\nBEGIN\n\n  %% Add connection to user files (if needed)\n\nEND Interface" > frama_c_wp_precisa/Interface.pvs
    fi
  
    OUTFILES="*.pvs"
    if [ ${#OUTFILES} ]; then
	for pvsfile in $OUTFILES
	do
	    # there are still some comments in why3 style in the generated PVS files
	    sed -i '' "s/(\*\(.*\)\*)/%\1/g" $pvsfile

	    # The importing of realized theories uses the why3 name, instead of the PVS name.
	    # The PVS name is used in the body of the theory though.
	    sed -i '' "s/IMPORTING \(.*\)\.\(.*\)\@/IMPORTING \1_\2@/g"  $pvsfile

            # replace theory and goal name
	    sed -i '' "s/wp_goal/${pvsfile%.pvs}/g"  $pvsfile
	done
    else
	echo "[RUN-FRAMAC] Frama-C didn't generate any new files."
    fi
    cd ..
else
    echo "[RUN-FRAMAC] Expected output directory 'interactive' does not exists."
fi

