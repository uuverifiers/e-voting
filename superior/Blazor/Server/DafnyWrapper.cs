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

using _module;
using Dafny;
using E_Voting.Transfer;
using System.Numerics;
using System.Text.Json;

namespace E_Voting
{
    public static class DafnyWrapper
    {
        public const string FaultyResult = "error";
        public const string NoVotes = "no_votes";
        public const string ErrorInDB = "db_error";

        private static bool CheckSize(BigInteger bigInteger)
        {
            return bigInteger < long.MaxValue && bigInteger > long.MinValue;
        }

        private static ISequence<BigInteger> GetCandidates(Election election)
        {
            BigInteger[] candidates = new BigInteger[election.Candidates.Count];
            for (int i = 0; i < candidates.Length; i++)
            {
                candidates[i] = election.Candidates[i].ID;
            }

            return Sequence<BigInteger>.FromArray(candidates);
        }

        private static ISequence<ISequence<BigInteger>> GetVotes(Election election)
        {
            BigInteger[][] tempVotes = new BigInteger[election.Votes.Count][];
            for (int i = 0; i < election.Votes.Count; i++)
            {
                string vote = election.Votes[i].Value;
                if(vote == "[]")
                {
                    tempVotes[i] = [];
                    continue;
                }

                BigInteger[] data = vote
                .Trim('[', ']')
                .Split(',')
                .Select(s => BigInteger.Parse(s.Trim()))
                .ToArray();
                tempVotes[i] = data;
            }

            ISequence<BigInteger>[] arrVotes = new ISequence<BigInteger>[tempVotes.Length];
            for (int i = 0; i < tempVotes.Length; i++)
            {
                arrVotes[i] = Sequence<BigInteger>.FromArray(tempVotes[i]);
            }

            return Sequence<ISequence<BigInteger>>.FromArray(arrVotes);
        }

        private static string BordaCount(Election election)
        {
            // inputs
            ISequence<BigInteger> candidates = GetCandidates(election);
            ISequence<ISequence<BigInteger>> votes = GetVotes(election);

            // outputs
            ISequence<BigInteger> tempSortedCandidates = Sequence<BigInteger>.Empty;
            IMap<BigInteger, BigInteger> tempResult = Map<BigInteger, BigInteger>.Empty;

            // parameter
            BigInteger tieBreakersBigInteger = new BigInteger(Convert.ToInt32(election.Parameter));

            // method call
            __default.BaldwinBordaCount(votes, candidates, tieBreakersBigInteger, out tempResult, out tempSortedCandidates);

            // serilaize
            Dictionary<long, int> result = new Dictionary<long, int>();
            foreach (var pair in tempResult.ItemEnumerable)
            {
                if(!CheckSize(pair.Car))
                {
                    throw new Exception("Invalid number!");
                }
                if (pair.Cdr > int.MaxValue || pair.Cdr < int.MinValue)
                {
                    throw new Exception("Invalid number!");
                }
                result.Add((long)pair.Car, (int)pair.Cdr);
            }

            return JsonSerializer.Serialize(result);
        }

        private static string STV(Election election)
        {
            // inputs
            ISequence<BigInteger> candidates = GetCandidates(election);
            ISequence<ISequence<BigInteger>> votes = GetVotes(election);

            // outputs
            ISequence<BigInteger> winners = Sequence<BigInteger>.Empty;
            ISequence<BigInteger> rest = Sequence<BigInteger>.Empty;

            // parameter
            BigInteger seatsBigInteger = new BigInteger(Convert.ToInt32(election.Parameter));

            // method call
            __default.SingleTransferableVote(votes, candidates, seatsBigInteger, out winners, out rest, out var dummy);

            // serilaize
            List<long> result = new List<long>();
            foreach (var winner in winners)
            {
                if (!CheckSize(winner))
                {
                    throw new Exception("Invalid number!");
                }
                result.Add((long)winner);
            }
            foreach (var winner in rest)
            {
                if (!CheckSize(winner))
                {
                    throw new Exception("Invalid number!");
                }
                result.Add((long)winner);
            }

            return JsonSerializer.Serialize(result);
        }

        private static string Evaluate(Election election)
        {
            switch (Help.GetVotingSystem(election.TypeID))
            {
                case VotingSystem.Borda_count: return BordaCount(election);
                case VotingSystem.Single_transferable_vote: return STV(election);
                default: throw new Exception("Unhandeled voting system!");
            }
        }

        private static string GetResult(Election election)
        {
            // if nobody voted
            if (election.Votes.Count == 0)
            {
                Database.DeleteElection(election.ID);
                Mail.SendVotersNoVoteElectionInfo(election);
                Log.Write("Election received no votes => No result calculated");

                return NoVotes;
            }

            Log.Write("Evaluating election... (ID: " + election.ID + ")");
            string result = "";
            try
            {
                result = Evaluate(election);
            }
            catch (Exception e)
            {
                Log.WriteError("Election was detected as faulty!");
                Log.Write(e.Message);
                Mail.SendVotersFaultyElectionInfo(election);
                Database.DeleteElection(election.ID);

                return FaultyResult;
            }

            Log.WriteSuccess("Election evaluated! => " + result);
            if (Database.InsertResult(result, election.ID))
            {
                Mail.SendVoterResultInfos(election);
                Log.WriteSuccess("Result saved to DB");
                return result;
            }
            else
            {
                Log.WriteError("DB error");
                return ErrorInDB;
            }
        }

        public static void Check()
        {
            while(true)
            {
                List<Election> elections = Database.GetDueElections();
                foreach(Election election in elections)
                {
                    GetResult(election);
                }

                Thread.Sleep(Config.EvaluationInterval * 1000);
            }
        }

        public static string GetResultNow(Election election)
        {
            Log.Write("Evaluation was requested by admin");

            if(election.Result != Config.EmptyResult)
            {
                Log.Write("Election already evaluated!");
                return election.Result;
            }

            return GetResult(election);
        }

        public static string GetResultForTests(Election election)
        {
            return Evaluate(election);
        }
    }
}
