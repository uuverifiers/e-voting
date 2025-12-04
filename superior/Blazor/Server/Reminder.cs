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

namespace E_Voting
{
    public static class Reminder
    {
        public static void Check()
        {
            while(true)
            {
                Log.Write("Sending reminders...");

                List<Election> elections = Database.GetElections(false, PrivacyLevel.Admin);
                foreach (Election election in elections)
                {
                    if(election.Result == Config.EmptyResult && 
                    election.End.AddDays(-Config.ReminderDaysBefore) <= DateTime.UtcNow)
                    {
                        foreach(Voter voter in election.Voters)
                        {
                            if(!voter.ReminderSent && !voter.Voted)
                            {
                                Mail.SendVoterReminder(election, voter);
                                Database.UpdateVoterReminder(voter.ID);
                            }
                        }
                    }
                }

                Log.WriteSuccess("Reminders done!");
                Thread.Sleep(Config.ReminderInterval * 1000);
            }
        }
    }
}
