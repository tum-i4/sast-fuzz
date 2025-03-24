# SASTFuzz

The following is a very brief outline of the steps required to run SASTFuzz.

**Please note that we will refine this README file for the final artifact submission, explaining each step in more detail.**

## Installation

1. Clone this repository locally.

2. Build the provided SASTFuzz-Docker image.

    ```bash
    docker build -f Dockerfile.dev -t sast-fuzz .
    ```

3. Once the Docker image is built, enter the container using the following command.

    ```bash
    docker run -it --mount type=bind,source=/path/to/transfer_dir,target=/mnt sast-fuzz /bin/bash
    ```

    Note that `transfer_dir` is a directory for the data transfer between the host system and the Docker container. It should also contain the cloned SASTFuzz sources.

4. Inside the container, run the `build.sh` script to build SASTFuzz.

    ```bash
    cd /mnt/sast-fuzz

    chmod +x build.sh
    ./build.sh
    ```

## Usage

### SAST Phase

In this phase, we run the SAST tools to identify potentally vulnerable code regions which we then use as fuzzing targets. Thereby, we first group the SAST-flagged lines at the basic block (BB) level (= target BBs), followed by assigning a vulnerability score to them that relfects how likely vulnerable they are.

Below, we show the execution steps for the subject program `pocketlang`.

1. Download the sources of `pocketlang`.

    ```bash
    cd /mnt

    git clone https://github.com/ThakeeNathees/pocketlang.git
    ```

2. Use [wllvm](https://github.com/travitch/whole-program-llvm) to compile `pocketlang` and output the corresponding LLVM Bitcode file.

    ```bash
    cd pocketlang

    export LLVM_COMPILER=clang
    export CC=wllvm

    make

    extract-bc ./build/Debug/bin/pocket
    mv ./build/Debug/bin/pocket.bc ./pocketlang.bc
    ```

3. Run the SASTFuzz-Inspector to extract the code properties of `pocketlang`.

    ```bash
    /mnt/sast-fuzz/build/sast-fuzz/static_analysis/inspection/src/sfi ./pocketlang.bc ./pocketlang.json
    ```

4. Run the SAST tools to identify the target BBs.

    ```bash
    cd /mnt/sast-fuzz/sast-fuzz/static_analysis/sast

    /root/.local/bin/poetry install

    /root/.local/bin/poetry run sfa --subject /mnt/pocketlang --inspection /mnt/pocketlang/pocketlang.json --tool clang-scan --tool codeql --tool semgrep --tool infer --tool flawfinder --grouping basic-block-v2 --parallel --output /mnt/pocketlang/pocketlang.csv
    ```

### Fuzzing Phase

1. Perform instrumentation for getting the target BB distance information

    ```bash
    cd /mnt/pocketlang

    /mnt/sast-fuzz/build/sast-fuzz/code_instrumentation/target_sites/src/cbi --targets=./pocketlang.csv ./pocketlang.bc
    ```

    This command produces the Bitcode file `pocketlang.ci.bc`. In addition, it produces `condition_info.txt` containing target location information.

2. Perform instrumentation for getting the code coverage information

    This instrumentation eventually outputs the fuzz binary based on the instrumented bitcode file from the previous instrumentation.

    ```bash
    export AFL_USE_ASAN=1

    /mnt/sast-fuzz/build/sast-fuzz/code_instrumentation/afl-clang-fast ./pocketlang.ci.bc -fPIC -lm -ldl -o ./pocketlang.sfz
    ```

3. Run SASTFuzz

    ```bash
    # export AFL_I_DONT_CARE_ABOUT_MISSING_CRASHES=1
    export AFL_SKIP_CPUFREQ=1

    /mnt/sast-fuzz/build/sast-fuzz/fuzzing/src/sast-fuzz -t 1000+ -d -m none -i /path/to/seed_corpus -o /mnt/output_dir -- /mnt/pocketlang/pocketlang.sfz @@
    ```
