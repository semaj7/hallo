open util/boolean

abstract sig Profile{
	name:one Name
}

sig PersonalProfile extends Profile{
	eMail:one EMail,
	friends:set PersonalProfile,
	following:set Profile,
	posted: set Content,
	isMember: set Member
}

sig Name{}
fact unique_names{all disjoint p,q:Profile | p.name != q.name}
fact names_are_connected{Name in Profile.name}

sig EMail{}
fact unique_Emails{all disjoint p,q:PersonalProfile | p.eMail != q.eMail}
fact eMail_are_connected{EMail in PersonalProfile.eMail}

fact no_reflexiv_friends{all p:Profile | not p in p.friends} 
fact no_reflexiv_followers{all p:Profile | not p in p.following}

sig GroupProfile extends Profile {}
//fact: every group has at least one admin
//can a member be member and follow a group?

sig Member {
	isAdmin:Bool,
	memberOf: one GroupProfile
}
fact unique_members{all disjoint p,q:PersonalProfile, m:Member | m in p.isMember => not m in q.isMember}
fact members_are_connected{Member in PersonalProfile.isMember}

sig Content{
	visible: Bool
}
fact unique_posts{all disjoint p,q:PersonalProfile, c:Content | c in p.posted => not c in q.posted}
fact post_are_connected{Content in PersonalProfile.posted}

abstract sig CommentableContent extends Content{}
abstract sig PersonalContent extends Content{}

sig Photo extends CommentableContent{}
sig Post extends CommentableContent{
	post: String,
	link: set Photo
}
sig comment extends CommentableContent{
	comment: String,
	refersTo: set CommentableContent
}

sig personalMessage extends PersonalContent{
	message: String,
	includedPhoto: lone Photo 	
}
sig personalDetails extends PersonalContent{}



pred show() {
	all p:PersonalProfile | #p.following >= 1
	all p:PersonalProfile | #p.friends >= 1
	all p:PersonalProfile | #p.posted >= 2
	some p:PersonalProfile | #p.isMember >= 2

//	#Photo >=5
	#PersonalProfile >= 2
//	#GroupProfile

}

run show for 7 but 2 Member
