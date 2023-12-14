#!/bin/bash

[ -z $1 ] \
    && echo "[RUN-FRAMAC] ❌ Error: no input file provided. Please provide a valid c file as the argument of this script" \
    && echo "[RUN-FRAMAC]           % "`basename $0` "<c-file>" \
    && exit 1;

[ ! -f $1 ] \
    && echo "[RUN-FRAMAC] ❌ Error: input file $1 not found. Please provide a valid c file as the argument of this script" \
    && echo "[RUN-FRAMAC]           % "`basename $0` "<c-file>" \
    && exit 1;

INPUT_FILE=$1

# Check REFLOW_HOME
#
[ ! -d "$REFLOW_HOME" ] \
    && echo "[RUN-FRAMAC] ❌ Error: the REFLOW_HOME variable does not point to a valid directory." \
    && echo "[RUN-FRAMAC]           Please set REFLOW_HOME to the installation directory of ReFlow." \
    && exit 1;

FRAMAC_WP_SHARE_FOLDER="$REFLOW_HOME/share/frama-c/wp"
ADHOC_WP_DRIVER=$FRAMAC_WP_SHARE_FOLDER/wp-reflow.driver

# Use reflow-specific drivers for why3
#
OPAM_EXE=opam

type $OPAM_EXE > /dev/null 2>&1
[ $? -ne 0 ] \
    && echo "[RUN-FRAMAC] ❌ Error: the opam executable is not reachable, please add it to your path." \
    && exit 1;

WHY3_DRIVERS=~/.opam/`opam switch show`/share/why3/drivers

[ ! -d "$WHY3_DRIVERS" ] \
    && echo "[RUN-FRAMAC] ❌ Error: couldn't find the share/why3 directory ($WHY3_DRIVERS didn't work)." \
    && exit 1;

TIMESTAMP=$(date +%s)

for file in $REFLOW_HOME/share/why3/drivers/*;do
    basefilename=`basename $file`
    if [ -f $WHY3_DRIVERS/$basefilename ]; then
	diff $file $WHY3_DRIVERS/$basefilename > /dev/null 2>&1
	[ $? -eq 0 ] && continue;

	# backup
        cp $WHY3_DRIVERS/$basefilename $WHY3_DRIVERS/$basefilename.$TIMESTAMP.bak
	[ $? -eq 1 ] && echo "[RUN-FRAMAC] ❌ Error: couldn't backup why3 drivers. Aborting" && exit 1;
    fi

    # copy file
    cp $file $WHY3_DRIVERS/$basefilename
done

# check frama-c availability
#
FRAMAC_EXE=frama-c

type $FRAMAC_EXE > /dev/null 2>&1
[ $? -ne 0 ] \
    && echo "Error: the Frama-C executable is not reachable, please add it to your path." \
    && exit 1;

# Run frama-c
#
$FRAMAC_EXE -wp \
	    -wp-timeout 0 \
	    -wp-prover pvs \
	    -wp-session $PWD \
	    -wp-out $PWD \
	    -wp-interactive edit \
	    -wp-model Typed+float \
	    -wp-driver $ADHOC_WP_DRIVER \
	    -wp-share $FRAMAC_WP_SHARE_FOLDER \
	    $INPUT_FILE

# Post-process output
#
if [ -d $PWD/"interactive" ]
then
    cd $PWD/interactive

    # The frama_c_wp_reflow/Interface.pvs file connects the
    # verification conditions with the PVS file that used as
    # input for PRECiSA. This connection is done manually for now.
    if [ ! -d frama_c_wp_reflow ]; then mkdir frama_c_wp_reflow; fi
    if [ ! -f "frama_c_wp_reflow/Interface.pvs" ]; then
	printf "%% Generated automatically by run-framac.sh\n%%\nInterface: THEORY\nBEGIN\n\n  %% Add connection to user files (if needed)\n\nEND Interface" > frama_c_wp_reflow/Interface.pvs
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

# Restore why3 drivers
for file in $REFLOW_HOME/share/why3/drivers/*;do
    basefilename=`basename $file`
    if [ -f $WHY3_DRIVERS/$basefilename.$TIMESTAMP.bak ]; then
	cp $WHY3_DRIVERS/$basefilename.$TIMESTAMP.bak $WHY3_DRIVERS/$basefilename
    fi
done
