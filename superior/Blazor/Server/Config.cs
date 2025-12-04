// Formally verified E-Voting using Dafny
// Copyright (C) 2025 Authors Superior Group
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as
// published by the Free Software Foundation, either version 3 of the
// License, or (at your option) any later version.
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
// See the GNU Affero General Public License for more details.
// You should have received a copy of the GNU Affero General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Xml.Linq;

namespace E_Voting
{
    public static class Config
    {
        private static bool enableLogging = false;
        private static string emptyResult = "";
        private static int voterTokenLength = 100;
        private static int adminTokenLength = 100;
        private static string fullDomain = "";
        private static string domain = "";

        private static int evaluationInterval = int.MaxValue;
        private static int reminderInterval = int.MaxValue;
        private static int cleanerInterval = int.MaxValue;

        private static string dbHost = "";
        private static int dbPort = 0;
        private static string dbUsername = "";
        private static string dbPassword = "";
        private static string dbName = "";

        private static int bordaCountMaxTieBreakers = 100;
        private static int stvMaxSeats = 100;

        private static string smtpServer = "";
        private static int smtpPort = 0;
        private static bool enableSSL = false;
        private static string smtpEmail = "";
        private static string smtpPassword = "";

        private static int reminderDaysBefore = 100;
        private static int electionCleanerThreshold = int.MaxValue;
        private static int logCleanerThreshold = int.MaxValue;

        private static string hostName = "N/A";
        private static string hostAddress = "N/A";
        private static string hostMail = "N/A";
        private static string complaintLink = "N/A";

        public static string SmtpServer => smtpServer;
        public static int SmtpPort => smtpPort;
        public static bool EnableSSL => enableSSL;
        public static string SmtpEmail => smtpEmail;
        public static string SmtpPassword => smtpPassword;
        public static bool EnableLogging => enableLogging;
        public static int EvaluationInterval => evaluationInterval;
        public static int ReminderInterval => reminderInterval;
        public static int ReminderDaysBefore => reminderDaysBefore;
        public static int CleanerInterval => cleanerInterval;
        public static string EmptyResult => emptyResult;
        public static int VoterTokenLength => voterTokenLength;
        public static int AdminTokenLength => adminTokenLength;
        public static string Domain => domain;
        public static string FullDomain => fullDomain;
        public static string DBHost => dbHost;
        public static int DBPort => dbPort;
        public static string DBUsername => dbUsername;
        public static string DBPassword => dbPassword;
        public static string DBName => dbName;
        public static int BordaCountMaxTieBreakers => bordaCountMaxTieBreakers;
        public static int StvMaxSeats => stvMaxSeats;
        public static int ElectionCleanerThreshold => electionCleanerThreshold;
        public static int LogCleanerThreshold => logCleanerThreshold;
        public static string HostName => hostName;
        public static string HostAddress => hostAddress;
        public static string HostMail => hostMail;
        public static string ComplaintLink => complaintLink;

        public static bool Load()
        {
            string configFile = @"../config.xml";
            string lol = Directory.GetCurrentDirectory();

            if (!File.Exists(configFile))
            {
                Log.WriteError("No config file found");
                return false;
            }

            try
            {
                XDocument doc = XDocument.Load(configFile);
                XElement root = doc.Element("config")!;

                enableLogging = bool.Parse(root.Element("enableLogging")!.Value);
                voterTokenLength = int.Parse(root.Element("voterTokenLength")!.Value);
                adminTokenLength = int.Parse(root.Element("adminTokenLength")!.Value);
                domain = root.Element("domain")!.Value;
                fullDomain = root.Element("fullDomain")!.Value;
                emptyResult = root.Element("emptyResult")!.Value;

                XElement thres = root.Element("thresholds")!;
                electionCleanerThreshold = int.Parse(thres.Element("electionCleanerThreshold")!.Value);
                logCleanerThreshold = int.Parse(thres.Element("logCleanerThreshold")!.Value);
                reminderDaysBefore = int.Parse(thres.Element("reminderDaysBefore")!.Value);

                XElement inter = root.Element("intervalls")!;
                evaluationInterval = int.Parse(inter.Element("evaluationInterval")!.Value);
                reminderInterval = int.Parse(inter.Element("reminderInterval")!.Value);
                cleanerInterval = int.Parse(inter.Element("cleanerInterval")!.Value);

                XElement db = root.Element("database")!;
                dbHost = db.Element("host")!.Value;
                dbPort = int.Parse(db.Element("port")!.Value);
                dbUsername = db.Element("username")!.Value;
                dbPassword = db.Element("password")!.Value;
                dbName = db.Element("name")!.Value;

                XElement alg = root.Element("algorithms")!;
                bordaCountMaxTieBreakers = int.Parse(alg.Element("bordaCountMaxTieBreakers")!.Value);
                stvMaxSeats = int.Parse(alg.Element("stvMaxSeats")!.Value);

                XElement mail = root.Element("mail")!;
                smtpServer = mail.Element("smtpServer")!.Value;
                smtpPort = int.Parse(mail.Element("smtpPort")!.Value);
                enableSSL = bool.Parse(mail.Element("enableSSL")!.Value);
                smtpEmail = mail.Element("smtpEmail")!.Value;
                smtpPassword = mail.Element("smtpPassword")!.Value;

                XElement con = root.Element("contact")!;
                hostName = con.Element("hostName")!.Value;
                hostAddress = con.Element("hostAddress")!.Value;
                hostMail = con.Element("hostMail")!.Value;
                complaintLink = con.Element("complaintLink")!.Value;

                return true;
            }
            catch (Exception e)
            {
                Log.WriteError("Failed to load config: " + e.Message);
                return false;
            }
        }
    }
}
