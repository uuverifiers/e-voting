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
using MySql.Data.MySqlClient;
using MySqlX.XDevAPI.Common;
using System.Xml.Linq;
using static System.Collections.Specialized.BitVector32;

namespace E_Voting
{
    public enum VotingSystem
    {
        Borda_count = 1,
        Single_transferable_vote = 2,
    }

    public enum PrivacyLevel
    {
        Public,
        Voters,
        Admin
    }

    public static class Database
    {
        private static string connectionString = "server=" + Config.DBHost + ";port=" + Config.DBPort + ";user=" + Config.DBUsername + ";password=" + Config.DBPassword + ";database=" + Config.DBName;

        public static bool CheckConnection()
        {
            try
            {
                using (MySqlConnection connection = new MySqlConnection(connectionString))
                {
                    connection.Open();
                }

                return true;
            }
            catch (Exception e)
            {
                Log.WriteError(e.Message);
                return false;
            }
        }

        public static long AddCandidate(string name, long election_id)
        {
            long newCandidate = -1;

            try
            {
                using (MySqlConnection connection = new MySqlConnection(connectionString))
                {
                    connection.Open();

                    string query = "INSERT INTO candidate (name, election_id) VALUES " +
                    "(@name, @election_id); " +
                    "SELECT LAST_INSERT_ID();";

                    using (MySqlCommand command = new MySqlCommand(query, connection))
                    {
                        command.Parameters.AddWithValue("@name", name);
                        command.Parameters.AddWithValue("@election_id", election_id);

                        newCandidate = Convert.ToInt64(command.ExecuteScalar());
                    }

                    connection.Close();
                }
            }
            catch (Exception e)
            {
                Log.WriteError(e.Message);
            }

            return newCandidate;
        }

        public static long AddVoter(string mail, long election_id)
        {
            long newVoter = -1;

            try
            {
                using (MySqlConnection connection = new MySqlConnection(connectionString))
                {
                    connection.Open();

                    while (newVoter == -1)
                    {
                        try
                        {
                            // Generate a new token each attempt
                            string token = RandomHelper.GetToken(Config.VoterTokenLength);

                            string query = @"
                            INSERT INTO voter (mail, token, election_id)
                            VALUES (@mail, @token, @election_id);
                            SELECT LAST_INSERT_ID();";

                            using (MySqlCommand command = new MySqlCommand(query, connection))
                            {
                                command.Parameters.AddWithValue("@mail", mail);
                                command.Parameters.AddWithValue("@token", token);
                                command.Parameters.AddWithValue("@election_id", election_id);

                                newVoter = Convert.ToInt64(command.ExecuteScalar());
                            }
                        }
                        catch (MySqlException e)
                        {
                            // duplicate entry error (token already used)
                            if (e.Number == 1062)
                            {
                                // try again with a new token
                                continue;
                            }
                            else
                            {
                                Log.WriteError(e.Message);
                                break;
                            }
                        }
                    }

                    connection.Close();
                }
            }
            catch (Exception e)
            {
                Log.WriteError(e.Message);
            }

            return newVoter;
        }

        public static Voter? CheckToken(string token)
        {
            Voter? voter = null;

            try
            {
                using (MySqlConnection connection = new MySqlConnection(connectionString))
                {
                    connection.Open();

                    string query =
                    "SELECT id, mail, token, voted, reminder_sent, election_id " +
                    "FROM voter " +
                    "WHERE token = @token;";

                    using (MySqlCommand command = new MySqlCommand(query, connection))
                    {
                        command.Parameters.AddWithValue("@token", token);

                        using (MySqlDataReader reader = command.ExecuteReader())
                        {
                            if (reader.Read())
                            {
                                voter = new Voter(
                                    reader.GetInt64("id"),
                                    reader.GetString("mail"),
                                    reader.GetString("token"),
                                    reader.GetBoolean("voted"),
                                    reader.GetBoolean("reminder_sent"),
                                    reader.GetInt64("election_id")
                                );
                            }
                        }
                    }

                    connection.Close();
                }
            }
            catch (Exception e)
            {
                Log.WriteError(e.Message);
            }

            return voter;
        }

        public static bool InsertResult(string result, long election_id)
        {
            try
            {
                using (MySqlConnection connection = new MySqlConnection(connectionString))
                {
                    connection.Open();

                    string query =
                    "UPDATE election SET result = @result " +
                    "WHERE id = @id;";

                    using (MySqlCommand command = new MySqlCommand(query, connection))
                    {
                        command.Parameters.AddWithValue("@id", election_id);
                        command.Parameters.AddWithValue("@result", result);

                        if (command.ExecuteNonQuery() <= 0)
                        {
                            return false;
                        }
                    }

                    connection.Close();
                }

                return true;
            }
            catch (Exception e)
            {
                Log.WriteError(e.Message);
                return false;
            }
        }

        public static bool Vote(long election_id, string value)
        {
            return Vote(election_id, value, -1);
        }

        public static bool Vote(long election_id, string value, long voter_id)
        {
            try
            {
                using (MySqlConnection connection = new MySqlConnection(connectionString))
                {
                    connection.Open();

                    using (MySqlTransaction transaction = connection.BeginTransaction())
                    {
                        string insertVoteQuery = 
                        "INSERT INTO vote (value, election_id) " +
                        "VALUES (@value, @election_id);";

                        using (MySqlCommand insertVoteCmd = new MySqlCommand(insertVoteQuery, connection, transaction))
                        {
                            insertVoteCmd.Parameters.AddWithValue("@election_id", election_id);
                            insertVoteCmd.Parameters.AddWithValue("@value", value);

                            if(insertVoteCmd.ExecuteNonQuery() <= 0)
                            {
                                return false;
                            }
                        }

                        if(voter_id != -1)
                        {
                            string updateVoterQuery =
                            "UPDATE voter SET voted = TRUE " +
                            "WHERE id = @voter_id;";

                            using (MySqlCommand updateVoterCmd = new MySqlCommand(updateVoterQuery, connection, transaction))
                            {
                                updateVoterCmd.Parameters.AddWithValue("@voter_id", voter_id);

                                if (updateVoterCmd.ExecuteNonQuery() <= 0)
                                {
                                    return false;
                                }
                            }
                        }

                        transaction.Commit();
                    }

                    connection.Close();
                }

                return true;
            }
            catch (Exception e)
            {
                Log.WriteError(e.Message);
                return false;
            }
        }

        public static List<Candidate> GetCandidates(long election_id)
        {
            List<Candidate> candidates = new List<Candidate>();

            try
            {
                using (MySqlConnection connection = new MySqlConnection(connectionString))
                {
                    connection.Open();

                    string query = "SELECT id, name, election_id " +
                    "FROM candidate " +
                    "WHERE election_id = @election_id;";

                    using (MySqlCommand command = new MySqlCommand(query, connection))
                    {
                        command.Parameters.AddWithValue("@election_id", election_id);

                        using (MySqlDataReader reader = command.ExecuteReader())
                        {
                            while (reader.Read())
                            {
                                candidates.Add(new Candidate(
                                    reader.GetInt64("id"),
                                    reader.GetString("name"),
                                    reader.GetInt64("election_id")
                                ));
                            }
                        }
                    }

                    connection.Close();
                }
            }
            catch (Exception e)
            {
                Log.WriteError(e.Message);
            }

            return candidates;
        }

        public static List<Vote> GetVotes(long election_id)
        {
            List<Vote> votes = new List<Vote>();

            try
            {
                using (MySqlConnection connection = new MySqlConnection(connectionString))
                {
                    connection.Open();

                    string query = "SELECT id, value, election_id " +
                    "FROM vote " +
                    "WHERE election_id = @election_id;";

                    using (MySqlCommand command = new MySqlCommand(query, connection))
                    {
                        command.Parameters.AddWithValue("@election_id", election_id);

                        using (MySqlDataReader reader = command.ExecuteReader())
                        {
                            while (reader.Read())
                            {
                                votes.Add(new Vote(
                                    reader.GetInt64("id"),
                                    reader.GetString("value"),
                                    reader.GetInt64("election_id")
                                ));
                            }
                        }
                    }

                    connection.Close();
                }
            }
            catch (Exception e)
            {
                Log.WriteError(e.Message);
            }

            return votes;
        }

        public static List<Voter> GetVoters(long election_id)
        {
            List<Voter> voters = new List<Voter>();

            try
            {
                using (MySqlConnection connection = new MySqlConnection(connectionString))
                {
                    connection.Open();

                    string query = "SELECT id, mail, token, voted, reminder_sent, election_id " +
                    "FROM voter " +
                    "WHERE election_id = @election_id;";

                    using (MySqlCommand command = new MySqlCommand(query, connection))
                    {
                        command.Parameters.AddWithValue("@election_id", election_id);

                        using (MySqlDataReader reader = command.ExecuteReader())
                        {
                            while (reader.Read())
                            {
                                voters.Add(new Voter(
                                    reader.GetInt64("id"),
                                    reader.GetString("mail"),
                                    reader.GetString("token"),
                                    reader.GetBoolean("voted"),
                                    reader.GetBoolean("reminder_sent"),
                                    reader.GetInt64("election_id")
                                ));
                            }
                        }
                    }

                    connection.Close();
                }
            }
            catch (Exception e)
            {
                Log.WriteError(e.Message);
            }

            return voters;
        }

        public static bool UpdateVoterReminder(long id)
        {
            try
            {
                using (MySqlConnection connection = new MySqlConnection(connectionString))
                {
                    connection.Open();

                    string query = "UPDATE voter SET reminder_sent = TRUE WHERE id = @id;";

                    using (MySqlCommand command = new MySqlCommand(query, connection))
                    {
                        command.Parameters.AddWithValue("@id", id);
                        if (command.ExecuteNonQuery() <= 0)
                        {
                            return false;
                        }
                    }

                    connection.Close();
                }

                return true;
            }
            catch (Exception e)
            {
                Log.WriteError(e.Message);
                return false;
            }
        }

        #region 'Elections'

        public static List<Election> GetDueElections()
        {
            // NOTE: The efficiency of the method needs to be improved if the website grows in popularity.
            // For now just using GetElections() is fine and much better for readability then having seperate logic.
            // In the future one could buffer IDs of due eletctions to decrease query size.

            List<Election> elections = GetElections(false, PrivacyLevel.Admin);
            List<Election> result = new List<Election>();

            foreach (Election election in elections)
            {
                // already evaluated
                if (election.Result != "none")
                {
                    continue;
                }

                // time has run out
                if (election.End < DateTime.UtcNow)
                {
                    result.Add(election);
                    continue;
                }

                if (election.EndWhenAllVoted)
                {
                    // not valid of there are no registered voters
                    if (election.Voters.Count == 0)
                    {
                        continue;
                    }

                    bool allVoted = true;
                    foreach (Voter voter in election.Voters)
                    {
                        if (!voter.Voted)
                        {
                            allVoted = false;
                            break;
                        }
                    }
                    if (allVoted)
                    {
                        result.Add(election);
                        continue;
                    }
                }
            }

            return result;
        }

        public static List<Election> GetPublicElections(bool raw)
        {
            // NOTE: The efficiency of the method needs to be improved if the website grows in popularity.
            // For now just using GetElections() is fine and much better for readability then having seperate logic.
            // In the future a seperate query that filters directly for public elections would be great.

            List<Election> elections = GetElections(raw, PrivacyLevel.Public);
            return elections.Where(e => e.PublicElection == true).ToList();
        }

        public static Election? CheckAdminToken(string adminToken)
        {
            return GetElection(adminToken, false, PrivacyLevel.Admin);
        }

        public static Election? GetElection(long id, bool raw, PrivacyLevel privacyLevel)
        {
            Election? election = GetRawElection(id, privacyLevel);
            if (election == null || raw || privacyLevel == PrivacyLevel.Public)
            {
                return election;
            }

            foreach (Candidate candidate in GetCandidates(election.ID))
            {
                election.AddCandidate(candidate);
            }
            foreach (Vote vote in GetVotes(election.ID))
            {
                election.AddVote(vote);
            }
            if (privacyLevel == PrivacyLevel.Admin)
            {
                foreach (Voter voter in GetVoters(election.ID))
                {
                    election.AddVoter(voter);
                }
            }

            return election;
        }

        public static Election? GetRawElection(long id, PrivacyLevel privacyLevel)
        {
            Election? election = null;

            try
            {
                using (MySqlConnection connection = new MySqlConnection(connectionString))
                {
                    connection.Open();

                    string query = "SELECT id, name, description, public, end_when_all_voted, end, type_id, result, admin_token, admin_mail, parameter " +
                                   "FROM election WHERE id = @id;";

                    using (MySqlCommand command = new MySqlCommand(query, connection))
                    {
                        command.Parameters.AddWithValue("@id", id);
                        using (MySqlDataReader reader = command.ExecuteReader())
                        {
                            if (reader.Read())
                            {
                                string name = reader.GetString("name");
                                string description = reader.GetString("description");
                                DateTime end = reader.GetDateTime("end");
                                bool isPublic = reader.GetBoolean("public");
                                bool endWhenAllVoted = reader.GetBoolean("end_when_all_voted");
                                int typeID = reader.GetInt32("type_id");
                                string result = reader.GetString("result");
                                string parameter = reader.GetString("parameter");
                                string admin_mail = reader.GetString("admin_mail");

                                string adminToken = reader.GetString("admin_token");
                                if (privacyLevel == PrivacyLevel.Admin)
                                {
                                    adminToken = reader.GetString("admin_token");
                                }
                                else
                                {
                                    adminToken = "private";
                                }

                                election = new Election
                                (
                                    id,
                                    name,
                                    description,
                                    end,
                                    isPublic,
                                    endWhenAllVoted,
                                    typeID,
                                    result,
                                    adminToken,
                                    admin_mail,
                                    parameter
                                );
                            }
                        }
                    }

                    connection.Close();
                }
            }
            catch (Exception e)
            {
                Log.WriteError(e.Message);
            }

            return election;
        }

        public static Election? GetElection(string admin_token, bool raw, PrivacyLevel privacyLevel)
        {
            Election? election = GetRawElection(admin_token, privacyLevel);
            if (election == null || raw || privacyLevel == PrivacyLevel.Public)
            {
                return election;
            }

            foreach (Candidate candidate in GetCandidates(election.ID))
            {
                election.AddCandidate(candidate);
            }
            foreach (Vote vote in GetVotes(election.ID))
            {
                election.AddVote(vote);
            }
            if (privacyLevel == PrivacyLevel.Admin)
            {
                foreach (Voter voter in GetVoters(election.ID))
                {
                    election.AddVoter(voter);
                }
            }

            return election;
        }

        public static Election? GetRawElection(string admin_token, PrivacyLevel privacyLevel)
        {
            Election? election = null;

            try
            {
                using (MySqlConnection connection = new MySqlConnection(connectionString))
                {
                    connection.Open();

                    string query = "SELECT id, name, description, public, end_when_all_voted, end, type_id, result, admin_token, admin_mail, parameter " +
                                   "FROM election WHERE admin_token = @admin_token;";

                    using (MySqlCommand command = new MySqlCommand(query, connection))
                    {
                        command.Parameters.AddWithValue("@admin_token", admin_token);
                        using (MySqlDataReader reader = command.ExecuteReader())
                        {
                            if (reader.Read())
                            {
                                int id = reader.GetInt32("id");
                                string name = reader.GetString("name");
                                string description = reader.GetString("description");
                                DateTime end = reader.GetDateTime("end");
                                bool isPublic = reader.GetBoolean("public");
                                bool endWhenAllVoted = reader.GetBoolean("end_when_all_voted");
                                int typeID = reader.GetInt32("type_id");
                                string result = reader.GetString("result");
                                string parameter = reader.GetString("parameter");
                                string admin_mail = reader.GetString("admin_mail");

                                if (privacyLevel != PrivacyLevel.Admin)
                                {
                                    admin_token = "private";
                                }

                                election = new Election
                                (
                                    id,
                                    name,
                                    description,
                                    end,
                                    isPublic,
                                    endWhenAllVoted,
                                    typeID,
                                    result,
                                    admin_token,
                                    admin_mail,
                                    parameter
                                );
                            }
                        }
                    }

                    connection.Close();
                }
            }
            catch (Exception e)
            {
                Log.WriteError(e.Message);
            }

            return election;
        }

        public static List<Election> GetElections(bool raw, PrivacyLevel privacyLevel)
        {
            if (raw)
            {
                return GetRawElections(privacyLevel);
            }
            else
            {
                List<Election> elections = GetRawElections(privacyLevel);
                if (privacyLevel == PrivacyLevel.Public)
                {
                    return elections;
                }

                foreach (Election election in elections)
                {
                    foreach (Candidate candidate in GetCandidates(election.ID))
                    {
                        election.AddCandidate(candidate);
                    }
                    foreach (Vote vote in GetVotes(election.ID))
                    {
                        election.AddVote(vote);
                    }
                    if (privacyLevel == PrivacyLevel.Admin)
                    {
                        foreach (Voter voter in GetVoters(election.ID))
                        {
                            election.AddVoter(voter);
                        }
                    }
                }

                return elections;
            }
        }

        private static List<Election> GetRawElections(PrivacyLevel privacyLevel)
        {
            List<Election> elections = new List<Election>();

            try
            {
                using (MySqlConnection connection = new MySqlConnection(connectionString))
                {
                    connection.Open();

                    string query = "SELECT id, name, description, public, end_when_all_voted, end, type_id, result, admin_token, admin_mail, parameter " +
                                   "FROM election;";

                    using (MySqlCommand command = new MySqlCommand(query, connection))
                    {
                        using (MySqlDataReader reader = command.ExecuteReader())
                        {
                            while (reader.Read())
                            {
                                long id = reader.GetInt64("id");
                                string name = reader.GetString("name");
                                string description = reader.GetString("description");
                                DateTime end = reader.GetDateTime("end");
                                bool isPublic = reader.GetBoolean("public");
                                bool endWhenAllVoted = reader.GetBoolean("end_when_all_voted");
                                int typeID = reader.GetInt32("type_id");
                                string result = reader.GetString("result");
                                string parameter = reader.GetString("parameter");
                                string admin_mail = reader.GetString("admin_mail");

                                string adminToken = reader.GetString("admin_token");
                                if (privacyLevel == PrivacyLevel.Admin)
                                {
                                    adminToken = reader.GetString("admin_token");
                                }
                                else
                                {
                                    adminToken = "private";
                                }

                                Election election = new Election
                                (
                                    id, 
                                    name, 
                                    description, 
                                    end, 
                                    isPublic, 
                                    endWhenAllVoted, 
                                    typeID, 
                                    result, 
                                    adminToken,
                                    admin_mail,
                                    parameter
                                );

                                elections.Add(election);
                            }
                        }
                    }

                    connection.Close();
                }
            }
            catch (Exception e)
            {
                Log.WriteError(e.Message);
            }

            return elections;
        }

        public static bool DeleteElection(long id)
        {
            try
            {
                using (MySqlConnection connection = new MySqlConnection(connectionString))
                {
                    connection.Open();

                    string query = "DELETE FROM election WHERE id = @id;";

                    using (MySqlCommand command = new MySqlCommand(query, connection))
                    {
                        command.Parameters.AddWithValue("@id", id);
                        if (command.ExecuteNonQuery() <= 0)
                        {
                            return false;
                        }
                    }

                    connection.Close();
                }

                Log.Write("Election deleted (ID: " + id + ")");
                return true;
            }
            catch (Exception e)
            {
                Log.WriteError(e.Message);
                return false;
            }
        }

        public static bool UpdateElectionDescription(long id, string description)
        {
            try
            {
                using (MySqlConnection connection = new MySqlConnection(connectionString))
                {
                    connection.Open();

                    string query = "UPDATE election SET description = @description WHERE id = @id;";

                    using (MySqlCommand command = new MySqlCommand(query, connection))
                    {
                        command.Parameters.AddWithValue("@description", description);
                        command.Parameters.AddWithValue("@id", id);
                        if (command.ExecuteNonQuery() <= 0)
                        {
                            return false;
                        }
                    }

                    connection.Close();
                }

                return true;
            }
            catch (Exception e)
            {
                Log.WriteError(e.Message);
                return false;
            }
        }

        public static bool UpdateElectionName(long id, string name)
        {
            try
            {
                using (MySqlConnection connection = new MySqlConnection(connectionString))
                {
                    connection.Open();

                    string query = "UPDATE election SET name = @name WHERE id = @id;";

                    using (MySqlCommand command = new MySqlCommand(query, connection))
                    {
                        command.Parameters.AddWithValue("@name", name);
                        command.Parameters.AddWithValue("@id", id);
                        if (command.ExecuteNonQuery() <= 0)
                        {
                            return false;
                        }
                    }

                    connection.Close();
                }

                return true;
            }
            catch (Exception e)
            {
                Log.WriteError(e.Message);
                return false;
            }
        }

        public static long AddElection(string name, string description, bool public_election, bool end_when_all_voted, DateTime end, int type_id, string admin_mail, string parameter, List<string> candidates, List<string> voters)
        {
            long newElection = -1;

            try
            {
                using (MySqlConnection connection = new MySqlConnection(connectionString))
                {
                    connection.Open();

                    while (newElection == -1)
                    {
                        // Generate a new token each attempt
                        string token = RandomHelper.GetToken(Config.AdminTokenLength);

                        try
                        {
                            string query = "INSERT INTO election (name, description, public, end_when_all_voted, end, type_id, admin_token, admin_mail, parameter) VALUES " +
                            "(@name, @description, @public, @end_when_all_voted, @end, @type_id, @admin_token, @admin_mail, @parameter); " +
                            "SELECT LAST_INSERT_ID();";

                            using (MySqlCommand command = new MySqlCommand(query, connection))
                            {
                                command.Parameters.AddWithValue("@name", name);
                                command.Parameters.AddWithValue("@description", description);
                                command.Parameters.AddWithValue("@public", public_election);
                                command.Parameters.AddWithValue("@end_when_all_voted", end_when_all_voted);
                                command.Parameters.AddWithValue("@end", end);
                                command.Parameters.AddWithValue("@type_id", type_id);
                                command.Parameters.AddWithValue("@admin_token", token);
                                command.Parameters.AddWithValue("@admin_mail", admin_mail);
                                command.Parameters.AddWithValue("@parameter", parameter);

                                newElection = Convert.ToInt64(command.ExecuteScalar());
                            }
                        }
                        catch (MySqlException e)
                        {
                            // duplicate entry error (token already used)
                            if (e.Number == 1062)
                            {
                                // try again with a new token
                                continue;
                            }
                            else
                            {
                                Log.WriteError(e.Message);
                                break;
                            }
                        }
                    }

                    connection.Close();
                }

                if (newElection != -1)
                {
                    foreach (string element in candidates)
                    {
                        AddCandidate(element, newElection);
                    }
                    foreach (string element in voters)
                    {
                        AddVoter(element, newElection);
                    }
                }
            }
            catch (Exception e)
            {
                Log.WriteError(e.Message);
            }

            return newElection;
        }

        #endregion
    }
}
