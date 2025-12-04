# formally-verified-evoting_blazor_app_group_superior

## What is this project?
Our project provides a secure online election platform built on formally verified algorithms. 
These are programs that have been proven to function correctly according to rigorous specifications, ensuring that every election outcome is accurate and trustworthy.
The algorithms were implemented and verified using **Dafny**, and the Dafny code was then transpiled into a C# library.
The **Dafny** code can be found in the wwwroot/Downloads folder.
The system is delivered as a **Blazor Server application**, providing a responsive and interactive web interface for voters.
We host the application using **NGINX**, which handles HTTPS connections to ensure secure and encrypted communication between voters and the server. 
This combination of formally verified algorithms, modern web technology, and secure hosting makes our platform a reliable choice for online elections.

## Setup
Follow these step-by-step instructions to get the project running:

1. **Clone the repository**

2. **Set up your database**
   - The project supports **MySQL/MariaDB**
   - Create a new schema for the application
   - Run the provided SQL statements

3. **Set up a mail service**
   - Configure any mail service of your choice
   - We used **Postfix**
     
4. **Set up a reverse proxy**
   - By default, the project only provides HTTP connections
   - We used **NGINX** to enable HTTPS

6. **Configure the application**
   - Open `config.xml`
   - Adjust all values to your environment, e.g., database user and password
   - Open `appsettings.json`
   - Adjust the Url to your needs

7. **Compile and run**
   - Compile the project for your target environment
   - The project is **cross-platform**

## Credits
This is a student project created as part of the **Computer Science major at the University of Regensburg**.

The project group, called **Superior Group** (inside joke), consisted of:
1. Patrick Janoschek
2. Ivana Kostadinovic
3. Robert Büttner
4. Henrik Oback

The exact contributions of each member are detailed in the project report.

## Licensing Information
Some files in this repository contain the GNU Affero General Public License (AGPL) header for uniformity, including files originally generated from project templates. 
Not all content in this repository is covered by the AGPL. 
Third-party libraries, fonts, and other assets included may be subject to different licenses as indicated in their respective documentation or source. 