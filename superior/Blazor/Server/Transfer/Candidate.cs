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

namespace E_Voting.Transfer
{
    public class Candidate
    {
        private long id;
        private string name;
        private long election_id;

        public long ID => id;
        public string Name => name;
        public long ElectionID => election_id;

        public Candidate(long id, string name, long election_id)
        {
            this.id = id;
            this.name = name;
            this.election_id = election_id;
        }
    }

}
