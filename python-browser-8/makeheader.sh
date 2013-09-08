#!/bin/bash

root_uid=`id -u root`
output_uid=`id -u `

pwd=`pwd`
echo "#define ROOT_UID $root_uid" > quarkexec.h
echo "#define OUTPUT_UID $output_uid" >> quarkexec.h
echo "#define TAB_PROGRAM_GATE \"$pwd/tab_exec_2\"" >> quarkexec.h
echo "#define TAB_PROGRAM \"$pwd/tab.py\"" >> quarkexec.h
echo "#define OUTPUT_PROGRAM \"$pwd/output.py\"" >> quarkexec.h
echo "int change_uid(int suid); " >> quarkexec.h

echo "quark_output_uid = $output_uid " > quarkexec.py


