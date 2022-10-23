# ContractCheck

Analysis tool for legal artifacts.

## Prerequisites

For the installation make sure that JDK newer than version 11 and Maven are installed on your system. This guide shows the process in Eclipse thus it is recommended to use a new version of Eclipse as your IDE.
You also need to install the <a href="https://github.com/z3prover/z3/pkgs/container/z3">Z3Prover</a> for the analysis.

## Installation

### Download Jobscheduler

```
git clone https://github.com/sen-uni-kn/JobScheduler
```

### Download ContractCheck

```
git clone https://github.com/sen-uni-kn/ContractCheck
```

### Import JobScheduler

- Select Existing Maven Projects and select the `JobScheduler-main` folder

- Deselect the root `.pom` (the tick at the very top) and leave every other box ticked. 

- Press Finish

Maven should now build the project. Wait until it's finished and proceed to the next step.

### Import ContractCheck

- Select Existing Maven Projects and select the `ContractCheck-main` folder.

- Press Finish

Maven should again build the project. After it's finished you may run the program.

### Add a private key

- Navigate to `legaltech.webeditor` and open `application.properties`.

- Generate a new keystore.p12 private key:

```
keytool -genkeypair -alias tomcat -keyalg RSA -keysize 2048 -storetype PKCS12 -keystore keystore.p12 -validity 3650
```
- Enter the password found in `application.properties` at `server.ssl.key-store-password`.

- You may skip the rest of the questions and confirm with `y` to finish.

- Move the keystore.p12 into the `legaltech.webeditor` folder.


### Run ContractCheck

- Navigate to `legaltech.webeditor` -> `src/main/java` -> `kn.uni.sen.joblibrary.legaltech.web` -> `LegalTechWebEditor.java`

- Run it with rightclick on `LegalTechWebEditor.java` as Java Application. You may need to authorize the connection by your Firewall.

- Open a browser of your choice (e.g. Firefox) and type https://localhost:8443/ into your main bar.

- Your Browser may warn you about a potential Security Risk. Press Advanced -> Accept and Continue.

- Type in the username and password found in `application.properties` at `spring.security.user.name` and `spring.security.user.password`

- You can now load a contract (e.g. `pretzelSPA_bad.json` in `src-LegalCheck/legaltech.job_legalcheck/src/test/resources`) via New Contract

### Z3 Installation Tips

If you experience trouble installing Z3 on your machine, you might want to try to install it via Python's `pip installer` which may take care of the Java bindings.
Alternatively you could also copy the necessary libraries of the pre-built releases into your `Java PATH` : 

`com.microsoft.z3.jar`
`libz3java.dll`
`libz3java.lib`
`libz3.lib`
`libz3.dll`