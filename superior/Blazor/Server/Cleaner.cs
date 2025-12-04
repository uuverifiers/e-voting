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
using static System.Collections.Specialized.BitVector32;

namespace E_Voting
{
    public static class Cleaner
    {
        public static void Check()
        {
            while(true)
            {
                Log.Write("Cleaning the log...");
                Log.Clear();

                Log.Write("Cleaning the database...");

                List<Election> elections = Database.GetElections(true, PrivacyLevel.Admin);
                foreach (Election election in elections)
                {
                    if(election.End.AddDays(Config.ElectionCleanerThreshold) < DateTime.UtcNow)
                    {
                        Database.DeleteElection(election.ID);
                    }
                }

                Log.WriteSuccess("Cleaning done!");
                Thread.Sleep(Config.CleanerInterval * 1000);
            }
        }
    }
}
