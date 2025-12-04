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

using E_Voting.Transfer;
using System;
using System.Diagnostics;
using System.Net;
using System.Net.Mail;
using static System.Collections.Specialized.BitVector32;

namespace E_Voting
{
    public static class Mail
    {
        public static void SendVotersFaultyElectionInfo(Election election)
        {
            string subject = "Faulty Election: " + election.Name;
            foreach (Voter voter in election.Voters)
            {
                string body = "An error or a manipulation attempt was detected! The election was deleted." + Environment.NewLine;
                body += Environment.NewLine;
                body += "Your token was: " + voter.Token;

                Send(voter.Mail, subject, body);
            }
        }

        public static void SendVotersNoVoteElectionInfo(Election election)
        {
            string subject = "No votes for Election: " + election.Name;
            foreach (Voter voter in election.Voters)
            {
                string body = "Nobody voted in this election! No result was calculated." + Environment.NewLine;
                body += Environment.NewLine;
                body += "Your token was: " + voter.Token;

                Send(voter.Mail, subject, body);
            }
        }

        public static void SendAdminInvitation(Election election)
        {
            string subject = "Election created!";
            string body = "Election Name: " + election.Name + Environment.NewLine;
            body += "Description: " + election.Description + Environment.NewLine;
            body += Environment.NewLine;

            body += "You can manage this election via this link" + Environment.NewLine;
            body += Config.FullDomain + "/admin/" + election.AdminToken + Environment.NewLine;
            body += Environment.NewLine;

            body += "If this link does not work, you can insert your admin token manually at" + Environment.NewLine;
            body += Config.FullDomain + "/admin" + Environment.NewLine;
            body += Environment.NewLine;

            body += "YOUR ADMIN TOKEN: " + election.AdminToken + Environment.NewLine;
            body += Environment.NewLine;

            body += "Election ends at " + election.End.ToString("dd.MM.yyyy HH:mm") + " (UTC)";

            Send(election.AdminMail, subject, body);
        }

        public static void SendVoterInvitations(Election election)
        {
            foreach(Voter voter in election.Voters)
            {
                SendVoterInvitation(election, voter);
            }
        }

        public static void SendVoterInvitation(Election election, Voter voter)
        {
            string subject = "You have been invited to vote";
            string body = "Election Name: " + election.Name + Environment.NewLine;
            body += "Description: " + election.Description + Environment.NewLine;
            body += Environment.NewLine;

            body += "You can vote via this link" + Environment.NewLine;
            body += Config.FullDomain + "/vote/" + voter.Token + Environment.NewLine;
            body += Environment.NewLine;

            body += "You can see election results via this link" + Environment.NewLine;
            body += Config.FullDomain + "/result/" + voter.Token + Environment.NewLine;
            body += Environment.NewLine;

            body += "If these links do not work, you can insert your voter token manually at" + Environment.NewLine;
            body += Config.FullDomain + "/insert" + Environment.NewLine;
            body += Environment.NewLine;

            body += "YOUR TOKEN: " + voter.Token + Environment.NewLine;
            body += Environment.NewLine;

            body += "Election ends at " + election.End.ToString("dd.MM.yyyy HH:mm") + " (UTC)";

            Send(voter.Mail, subject, body);
        }

        public static void SendVoterResultInfos(Election election)
        {
            foreach (Voter voter in election.Voters)
            {
                SendVoterResultInfo(election, voter);
            }
        }

        public static void SendVoterReminder(Election election, Voter voter)
        {
            string subject = "Reminder: Election ends in " + Config.ReminderDaysBefore + " days!";
            string body = "Election Name: " + election.Name + Environment.NewLine;
            body += "Description: " + election.Description + Environment.NewLine;
            body += Environment.NewLine;

            body += "You can vote via this link" + Environment.NewLine;
            body += Config.FullDomain + "/vote/" + voter.Token + Environment.NewLine;
            body += Environment.NewLine;

            body += "If this link does not work, you can insert your voter token manually at" + Environment.NewLine;
            body += Config.FullDomain + "/insert" + Environment.NewLine;
            body += Environment.NewLine;

            body += "YOUR TOKEN: " + voter.Token + Environment.NewLine;

            Send(voter.Mail, subject, body);
        }

        public static void SendVoterResultInfo(Election election, Voter voter)
        {
            string subject = "Election is over";
            string body = "Election Name: " + election.Name + Environment.NewLine;
            body += "Description: " + election.Description + Environment.NewLine;
            body += Environment.NewLine;

            body += "You can see election results via this link" + Environment.NewLine;
            body += Config.FullDomain + "/result/" + voter.Token + Environment.NewLine;
            body += Environment.NewLine;

            body += "If this link does not work, you can insert your voter token manually at" + Environment.NewLine;
            body += Config.FullDomain + "/insert" + Environment.NewLine;
            body += Environment.NewLine;

            body += "YOUR TOKEN: " + voter.Token + Environment.NewLine;

            Send(voter.Mail, subject, body);
        }

        private static void Send(string recipient, string subject, string body)
        {
            Task.Run(() => SendTask(recipient, subject, body));
        }

        private static void SendTask(string recipient, string subject, string body)
        {
            // NOTE: To increase the rate of successful mail delivery one could add a
            // resend service here. One that tracks unsend mails and tries to resend them later.

            try
            {
                Log.Write("Sending mail to '" + recipient + "' ...");
                using (SmtpClient client = new SmtpClient(Config.SmtpServer, Config.SmtpPort))
                {
                    if(Config.EnableSSL)
                    {
                        client.Credentials = new NetworkCredential(Config.SmtpEmail, Config.SmtpPassword);
                        client.EnableSsl = true;
                    }
                    else
                    {
                        client.Credentials = null;
                        client.EnableSsl = false;
                    }

                    MailMessage mailMessage = new MailMessage();
                    mailMessage.From = new MailAddress("noreply@" + Config.Domain);
                    mailMessage.To.Add(recipient);
                    mailMessage.Subject = subject;
                    mailMessage.Body = body;

                    client.Send(mailMessage);
                }
                Log.WriteSuccess("Send!");
            }
            catch (Exception e)
            {
                Log.WriteError(e.Message);
            }
        }
    }
}
