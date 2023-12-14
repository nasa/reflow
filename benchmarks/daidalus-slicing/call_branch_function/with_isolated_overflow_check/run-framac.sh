#!/bin/bash

ADHOC_WP_DRIVER=wp-nasalib

if [ -f "$1" ]; then

    OUTPUTDIR=interactive

    # if [ -d "$OUTPUTDIR" ]; then
    # 	if [ -d "$OUTPUTDIR.bak" ]; then
    # 	    rm -r "./$OUTPUTDIR.bak"
    # 	fi
    # 	mv "$OUTPUTDIR" "$OUTPUTDIR.bak"
    # fi
    
    frama-c \
	-wp \
	-wp-timeout 2 \
	-wp-prover pvs \
	-wp-session . \
	-wp-out . \
	-wp-interactive edit \
	-wp-model Typed+float \
	-wp-share wp-drivers \
	-wp-driver $ADHOC_WP_DRIVER.driver \
	$1
    
    if [ -d "$OUTPUTDIR" ]
    then
	# framac.20.0 is generating pvs files with .why extension
	cd "$OUTPUTDIR"
	OUTFILES="*.pvs"
	if (( ${#OUTFILES} )) ; then
	    for pvsfile in $OUTFILES
	    do
		BNAME=$(basename -- "$pvsfile")
		FNAME="${BNAME%.*}"
		# the theory and the theorem are called wp_goal; I rename it to
		# the filename so we can use provethem on all the generated VCs.
		sed -i '' "s/wp_goal/$FNAME/g" $pvsfile
		
		# there are still some comments in why3 style
		sed -i '' "s/(\*\(.*\)\*)/%\1/g" $pvsfile
		
		# The importing of realized theories uses the why3 name, instead of the PVS name.
		# The PVS name is used in the body of the theory though.
		sed -i '' "s/IMPORTING \(.*\)\.\(.*\)\@/IMPORTING \1_\2@/g"  $pvsfile
		
	    done
	else
	    echo "[RUN-FRAMAC] Frama-C didn't generate any new files."
	fi
	cd ..
    else
	echo "[RUN-FRAMAC] Expected output directory \"$OUTPUTDIR\" does not exists."
    fi
    
else
    if [ $1 ]; then
	echo File $1 not found.
    else
	echo Please provide the filename to be analyzed.
    fi
fi
