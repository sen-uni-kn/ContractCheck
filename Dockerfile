FROM eclipse-temurin:11-jdk-jammy

# Number of make jobs, we recommend to set this to the number of cores (z3 needs a decade to compile otherwise)
ARG JOBS=1

RUN apt update && apt install -y --no-install-recommends \
    build-essential \
    maven \
    python3 \
    python-is-python3

# Install z3 with java bindings
WORKDIR /deps
RUN wget https://github.com/Z3Prover/z3/archive/refs/tags/z3-4.12.1.tar.gz
RUN tar -xzf z3-4.12.1.tar.gz
RUN rm z3-4.12.1.tar.gz
WORKDIR /deps/z3-z3-4.12.1
RUN python scripts/mk_make.py --java
WORKDIR /deps/z3-z3-4.12.1/build
RUN make -j${JOBS}
RUN make install

# Install jobscheduler
WORKDIR /deps
COPY library_jobscheduler ./library_jobscheduler
COPY install_jobscheduler.sh .
RUN /bin/bash install_jobscheduler.sh

# Install ContractCheck
WORKDIR /contractcheck
COPY src_LegalCheck/ .
RUN mvn clean install -DskipTests
