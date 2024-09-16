#!/bin/bash




while read line
do
    if [ "${line:0:25}" = "Verification result: TRUE" ]
    then
        exit 0
    fi
done 


	exit 1
fi

