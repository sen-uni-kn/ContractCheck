#!/bin/bash

declare -A JOBSCHEDULER_LIBS=( ["jobscheduler.common"]=TRUE ["jobscheduler.console"]=FALSE ["jobscheduler.core"]=FALSE )
VERSION="1.6.0"

for lib in "${!JOBSCHEDULER_LIBS[@]}"; do
    mvn install:install-file \
        -Dfile=library_jobscheduler/${lib}-${VERSION}.jar \
        -DgroupId=kn.uni.sen.jobscheduler \
        -DartifactId=${lib} \
        -Dversion=${VERSION} \
        -Dpackaging=jar \
        -DgeneratePom=true

    if [ "${JOBSCHEDULER_LIBS[$lib]}" = TRUE ]; then
        mvn install:install-file \
            -Dfile=library_jobscheduler/${lib}-${VERSION}-tests.jar \
            -DgroupId=kn.uni.sen.jobscheduler \
            -DartifactId=${lib} \
            -Dversion=${VERSION} \
            -Dpackaging=jar \
            -Dclassifier=tests \
            -DgeneratePom=true
    fi
done