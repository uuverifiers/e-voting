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
using Microsoft.JSInterop;
using QRCoder;

namespace E_Voting
{
    public static class Help
    {
        public static bool IsPrefListElection(VotingSystem system)
        {
            switch (system)
            {
                case VotingSystem.Borda_count:
                case VotingSystem.Single_transferable_vote:
                    return true;
                default:
                    return false;
            }
        }

        public static bool IsListResultElection(VotingSystem system)
        {
            switch (system)
            {
                case VotingSystem.Borda_count:
                    return true;
                default:
                    return false;
            }
        }

        public static bool IsSetResultElection(VotingSystem system)
        {
            switch (system)
            {
                case VotingSystem.Single_transferable_vote:
                    return true;
                default:
                    return false;
            }
        }

        public static VotingSystem GetVotingSystem(int typeID)
        {
            if (Enum.IsDefined(typeof(VotingSystem), typeID))
            {
                return (VotingSystem)typeID;
            }
            else
            {
                throw new Exception("Invalid enum key!");
            }
        }

        public static int GetTypeID(VotingSystem system)
        {
            return (int)system;
        }

        public static string GetSystemName(VotingSystem system)
        {
            switch(system)
            {
                case VotingSystem.Borda_count: return "Borda Count";
                case VotingSystem.Single_transferable_vote: return "Single Transferable Vote";
                default: return "not found";
            }
        }

        public static string GetSystemURL(VotingSystem system)
        {
            switch (system)
            {
                case VotingSystem.Borda_count: return "borda-count";
                case VotingSystem.Single_transferable_vote: return "stv";
                default: return "none";
            }
        }

        public static string GenerateQrCodeSvg(string text)
        {
            using var qrGenerator = new QRCodeGenerator();
            using var qrData = qrGenerator.CreateQrCode(text, QRCodeGenerator.ECCLevel.Q);
            using var qrCode = new SvgQRCode(qrData);
            return qrCode.GetGraphic(5);
        }

        public static async Task DisplayMessage(IJSRuntime js, string text)
        {
            try
            {
                await js.InvokeVoidAsync("alert", text);
            }
            catch(Exception e)
            {
                Log.Write("JS alert has failed: " + e.Message);
            }
        }

        public static async Task DisplayDatabaseError(IJSRuntime js)
        {
            await DisplayMessage(js, "Database error!");
        }

        public static string CutSize(string text, int max)
        {
            if(text.Length <= max)
            {
                return text;
            }
            return text.Substring(0, max) + "...";
        }
    }
}
